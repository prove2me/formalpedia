-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_BinaryAdder_adderFullLoop_correct_and_cost
-- name    : TwoAgentSched.TotalTotal.BinaryAdder.adderFullLoop_correct_and_cost
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:05:00.61432+00:00
-- url     : https://prove2.me/theorems/d1d5dd38-8a5c-483b-80a5-3a1039608f30
-- title:
--   Unpadded binary stack addition: exact execution and arithmetic correctness
-- statement:
--   Let $a$ and $b$ be finite little-endian Boolean words, possibly of different lengths, and let $c$ be an input carry bit. Write $L=\max(|a|,|b|)$. The unpadded finite-stack adder treats an absent input digit as zero and must satisfy both claims below.
--
--   1. It consumes both input stacks in exactly $3L+1$ source-program steps, leaves the emitted low sum bits in reverse order on the output stack, and leaves the final carry on top of the carry stack.
--   2. If $s$ denotes the little-endian low output word and $c_{\mathrm{out}}$ the final carry, then
--
--   $$
--   \operatorname{val}(a)+\operatorname{val}(b)+c
--    =\operatorname{val}(s)+2^L c_{\mathrm{out}}.
--   $$
--
--   This unequal-length adder is needed to accumulate the integer scheduling thresholds in the binary transducer. The already verified equal-length adder does not cover this case. This statement does not by itself prove a complete polynomial-time reduction.
-- source:
--   Supporting binary arithmetic for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. The concrete adder and exact execution bound are auxiliary formalization obligations, not claims from the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdder

namespace TwoAgentSched.TotalTotal.BinaryAdder

open CookPvsNP ProjSchedTW.Complexity

theorem adderFullLoop_correct_and_cost (left right : List Bool) (c : Bool)
    (output carries : List BSym) :
    ∃ finalCarryTail : List BSym,
      adderFullLoop.Exec
        (store (left.map bitSym) (right.map bitSym) output (bitSym c :: carries))
        (store [] [] (((addFullAux left right c).1.map bitSym).reverse ++ output)
          (bitSym (addFullAux left right c).2 :: finalCarryTail))
        (3 * max left.length right.length + 1) ∧
      bitWordValue left + bitWordValue right + bitValue c =
        bitWordValue (addFullAux left right c).1 +
          2 ^ (max left.length right.length) * bitValue (addFullAux left right c).2 := by sorry

end TwoAgentSched.TotalTotal.BinaryAdder
