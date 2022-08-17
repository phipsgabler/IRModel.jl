module IRModel

using AbstractPPL
using MacroTools: MacroTools
using Setfield

const MT = MacroTools

function __tilde__ end
function __vn__ end


function transformed_ir(mod, body)
    newbody = MT.postwalk(body) do x
        if MT.@capture(x, {vn_})
            return Expr(:call, __vn__, QuoteNode(AbstractPPL.varname(vn)))
        else
            return x
        end
    end
    
    ir = only(Meta.lower(mod, newbody).args)
    map!(ir.code, ir.code) do line
        if Meta.isexpr(line, :call, 2) && line.args[1] == __vn__
            return Expr(:braces, AbstractPPL.drop_escape(line.args[2].value))
        elseif Meta.isexpr(line, :call, 2) && line.args[1] == :(~)
            return Expr(:(~), line.args[2:end]...)
        else
            return line
        end
    end

    return ir
end


function irmodel(mod, expr)
    fundef = MT.splitdef(expr)
    name = fundef[:name]
    args = map(MT.splitarg, fundef[:args])
    kwargs = map(MT.splitarg, fundef[:kwargs])
    rtype = get(fundef, :rtype, :Any)
    whereparams = fundef[:whereparams]
    body = fundef[:body]

    ir = transformed_ir(mod, body)

    resolve(expr::Expr) = Expr(expr.head, resolve.(expr.args)...)
    resolve(s::Core.SlotNumber) = ir.slotnames[s.id]
    resolve(v::Core.SSAValue) = v #Symbol("%", v.id)
    resolve(x) = x
    jumplabel(i) = Symbol("#", i)

    blocks = Expr[]
    function push_line!(block, expr)
        if length(blocks) < block
            push!(blocks, Expr(:block, :(@label $(jumplabel(length(blocks) + 1)))))
        end
        
        push!(blocks[end].args, expr)
    end

    # add all lines to blocks, but leaving control flow statements intact
    current_block = 1
    for i in eachindex(ir.code)
        line = ir.code[i]
        if line isa Core.GotoNode || line isa Core.GotoIfNot || line isa Core.ReturnNode
            push_line!(current_block, line)
            current_block += 1
        elseif Meta.isexpr(line, :(=))
            push_line!(current_block, Expr(:(=), resolve(line.args[1]), resolve.(line.args[2:end])...))
        else
            # push_line!(current_block, :($(Symbol("%", i)) = $(resolve(line))))
            push_line!(current_block, :($(Core.SSAValue(i)) = $(resolve(line))))
        end
    end

    # figure out block ranges
    block_ranges = UnitRange{Int}[]
    previous_block_end = 0
    for block in blocks
        block_end = previous_block_end + length(block.args) - 1
        push!(block_ranges, (previous_block_end + 1):block_end)
        previous_block_end = block_end
    end

    # replace control flow statements using block numbers
    line2block(i) = findfirst(u -> i ∈ u, block_ranges)
    for block in blocks
        for i in eachindex(block.args)
            line = block.args[i]
            if line isa Core.GotoNode
                block.args[i] = :(@goto $(jumplabel(line2block(line.label))))
            elseif line isa Core.GotoIfNot
                block.args[i] = :($(resolve(line.cond)) || @goto $(jumplabel(line2block(line.dest))))
            elseif line isa Core.ReturnNode
                block.args[i] = :(return $(line.val))
            end
        end
    end

    # reinsert line numbers
    code = MT.striplines(Expr(:block, blocks...))
    # TODO: linetable, codelocs

    return (;ir, code, args)
    # return QuoteNode(MT.identity(code))
end

macro irmodel(expr)
    return irmodel(__module__, expr)
end


end # module
