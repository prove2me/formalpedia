-- Prove2me | Theorems.Thm_TwoAgentSched_sortC_spec
-- name    : TwoAgentSched.sortC_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:52:36.726057+00:00
-- url     : https://prove2.me/theorems/0b166220-2123-41e0-a376-54ea4bbd4b6f
-- title:
--   p. 233: sorting $J^B$ by deadline in $O(n_B\log n_B)$
-- statement:
--   There is an absolute constant $C$ such that, for every list $xs$ and every key map into a linearly ordered set, merge sort in the cost model
--
--   1. returns a permutation of $xs$,
--   2. in nondecreasing order of the key,
--   3. using at most
--   $$
--   C\cdot |xs| \cdot \log |xs|
--   $$
--   unit-cost steps (comparisons, elements moved, split steps).
--
--   Applied to the B-jobs keyed by their deadlines, this orders $J^B$ a priori in time $O(n_B\log n_B)$.
--
--   Differences from the source:
--   - generalization: ordering J^B by the deadlines D^B_k → sorting any list by any key into any linearly ordered type; reason: J^B keyed by the deadlines (or by their reverse order, as the algorithm uses) is an instance
--   - reading: time, assuming each f^A_h(·) value can be computed in constant time and the deadlines are available (p. 233) → the cost of the Timed run: one step per real addition or subtraction, per comparison (reals, cuts), per evaluation f^A_h(t), per deadline lookup, per list cell traversed, consed or moved, per relation query or array access; reason: the unit-cost RAM model with the paper's constant-time assumptions; the deadlines are an input, as in the paper's case where f^B_k^{-1} is available
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("The job set J^B can be ordered a priori, in nondecreasing order of deadlines D^B_k, in time O(n_B log n_B)")

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_sortC

namespace TwoAgentSched

/-- **Sorting the B-jobs by deadline in `O(n_B log n_B)`** (Agnetis–Mirchandani–Pacciarelli–
Pacifici, Oper. Res. 52(2) (2004), p. 233: "The job set `J^B` can be ordered a priori, in
nondecreasing order of deadlines `D^B_k`, in time `O(n_B log n_B)`"). There is one absolute
constant `C` such that for every list `xs` and every key into a linearly ordered type, the merge
sort `sortC` returns a permutation of `xs` in nondecreasing order of the key, at cost at most
`C · |xs| · log |xs|` (comparisons, elements moved, split steps). -/
theorem sortC_spec :
    ∃ C : ℝ, ∀ (β κ : Type) [LinearOrder κ] (key : β → κ) (xs : List β),
      (sortC key xs).val.Perm xs ∧
      (sortC key xs).val.Pairwise (fun a b => key a ≤ key b) ∧
      ((sortC key xs).cost : ℝ) ≤ C * (xs.length : ℝ) * Real.log (xs.length : ℝ) := by sorry

end TwoAgentSched
