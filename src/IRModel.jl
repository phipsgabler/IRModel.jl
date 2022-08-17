module IRModel

using AbstractPPL
using MacroTools: MacroTools
using Setfield

const MT = MacroTools

function __tilde__ end
function __vn__ end


function irmodel(mod, expr)
    fundef = MT.splitdef(expr)
    name = fundef[:name]
    args = map(MT.splitarg, fundef[:args])
    kwargs = map(MT.splitarg, fundef[:kwargs])
    rtype = get(fundef, :rtype, :Any)
    whereparams = fundef[:whereparams]
    body = fundef[:body]

    newbody = MT.postwalk(body) do x
        if MT.@capture(x, ~(lhs_, rhs_))
            return Expr(:call, __tilde__, lhs, rhs)
        elseif MT.@capture(x, {vn_})
            return Expr(:call, __vn__, QuoteNode(AbstractPPL.varname(vn)))
        else
            return x
        end
    end

    ir = only(Meta.lower(mod, newbody).args)
    map!(ir.code, ir.code) do line
        if Meta.isexpr(line, :call, 3) && line.args[1] == __tilde__
            # return line
            return Expr(:call, :~, line.args[2:3]...)
        elseif Meta.isexpr(line, :call, 2) && line.args[1] == __vn__
            return Expr(:braces, AbstractPPL.drop_escape(line.args[2].value))
        else
            return line
        end
    end

    resolve(expr::Expr) = Expr(expr.head, resolve.(expr.args)...)
    resolve(s::Core.SlotNumber) = ir.slotnames[s.id]
    resolve(v::Core.SSAValue) = Symbol(v.id)
    resolve(x) = x
    jumplabel(i) = Meta.quot(Symbol("#", i))
    
    expr_lines = []
    jump_targets = Set{Int}()

    function push_line!(i, expr)
        if i in jump_targets
            return push!(expr_lines, :(@label $(jumplabel(i)) $expr))
        else
            return push!(expr_lines, expr)
        end
    end

    current_block = 1
    for i in eachindex(ir.code)
        line = ir.code[i]
        if line isa Core.GotoNode
            push!(jump_targets, line.label)
            push_line!(i, :(@goto $(jumplabel(line.label))))
            current_block += 1
        elseif line isa Core.GotoIfNot
            push!(jump_targets, line.dest)
            push_line!(line, :($(line.cond) || @goto $(jumplabel(line.dest))))
            current_block += 1
        elseif line isa Core.ReturnNode
            push_line!(i, :(return $(line.val)))
            current_block += 1
        elseif Meta.isexpr(line, :(=))
            push_line!(i, Expr(:(=), resolve(line.args[1]), resolve.(line.args[2:end])...))
        else
            push_line!(i, :($(Symbol("%", i)) = $(resolve(line))))
        end
    end

    code = MT.striplines(Expr(:block, expr_lines...))

    # return (;ir, code, args)
    return QuoteNode(code)
end

macro irmodel(expr)
    return irmodel(__module__, expr)
end


end # module
