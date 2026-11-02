-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_stack_tagged_gadget_exec
-- name    : TwoAgentSched.TotalTotal.stack_tagged_gadget_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:14:20.563927+00:00
-- url     : https://prove2.me/theorems/de0e1d3b-5dc8-4bab-9bd7-729e2ffe2f13
-- title:
--   A finite stack program writes a tagged PARTITION weight in linear time
-- statement:
--   Given the canonical binary code of a positive integer $m$ and two counter stacks of lengths $i$ and $d$, the finite stack program $P$ halts after exactly $5i+5d+9$ source-program steps. It consumes both counters and leaves the output stack containing
--
--   $$
--   \operatorname{enc}\!\left(2(4^{i+d+1}m+4^i)\right).
--   $$
--
--   This is one explicit, linearly bounded component of the distinct-even PARTITION gadget used in the scheduling encoding reduction. The counters must already be available and the initial output must already contain the canonical code of $m$. The result does not assert that a complete reduction transducer, including parsing, sorting, and threshold computation, has been constructed.
--
--   **Formalization Note** The first two stacks supply the counter lengths, their symbol values being immaterial. The third stack starts with the separator-terminated least-significant-bit-first code.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2 and proof, pp. 237–238. The distinct-even PARTITION gadget and this explicit stack-program component are additional supporting constructions, not claims stated in the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_StackTaggedOutput

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity StackTaggedOutput

theorem stack_tagged_gadget_exec (i d : List BSym) (m : ℕ) (hm : 0 < m) :
    taggedOutput.Exec (store i d (encNat m))
      (store [] [] (encNat (2 * (4 ^ (i.length + d.length + 1) * m + 4 ^ i.length))))
      (5 * i.length + 5 * d.length + 9) := by sorry

end TwoAgentSched.TotalTotal
