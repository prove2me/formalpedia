-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_StackCompareDigits_correct_and_total
-- name    : TwoAgentSched.TotalTotal.StackCompareDigits.correct_and_total
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:38:55.451214+00:00
-- url     : https://prove2.me/theorems/48b5c0ef-d483-4aa0-8487-26f51099ad8e
-- title:
--   A finite stack program compares canonical binary naturals in linear time
-- statement:
--   The finite stack comparator has two properties.
--
--   1. Given the most-significant-bit-first canonical binary digit strings of natural numbers $m$ and $n$ and an initial equality marker, it halts with a less marker at the top of its result stack if and only if $m<n$. The execution takes at most
--
--   $$
--   3\min(|\operatorname{bits}(m)|,|\operatorname{bits}(n)|)+5
--   $$
--
--   source steps.
--   2. On arbitrary symbol stacks, including nonbinary data and an empty state stack, it halts within the same expression using the two input-stack lengths.
--
--   The comparator is a reusable sorting component for the scheduling reduction. The arbitrary-input clause asserts termination only; the numerical correctness clause applies to canonical binary representations.
-- source:
--   Supporting implementation for the formalization of Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This concrete comparator and its bounds are auxiliary formalization results, not claims from the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_StackCompareDigits

namespace TwoAgentSched.TotalTotal.StackCompareDigits

open CookPvsNP ProjSchedTW.Complexity

theorem correct_and_total :
    (∀ m n : ℕ, ∃ (steps : ℕ) (left right result : List BSym),
      steps ≤ 3 * min m.bits.length n.bits.length + 5 ∧
      compareFullProg.Exec
        (store (m.bits.reverse.map digitSym) (n.bits.reverse.map digitSym) [.sep])
        (store left right result) steps ∧
      (result.head? = some .zero ↔ m < n)) ∧
    (∀ left right states : List BSym, ∃ (out : Fin 3 → List BSym) (steps : ℕ),
      compareFullProg.Exec (store left right states) out steps ∧
        steps ≤ 3 * min left.length right.length + 5) := by sorry

end TwoAgentSched.TotalTotal.StackCompareDigits
