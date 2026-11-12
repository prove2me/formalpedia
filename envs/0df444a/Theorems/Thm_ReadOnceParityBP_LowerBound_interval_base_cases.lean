-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_interval_base_cases
-- name    : ReadOnceParityBP.LowerBound.interval_base_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:02.804507+00:00
-- url     : https://prove2.me/theorems/716cb5a2-1599-43b1-b4e6-968cdd13c07c
-- title:
--   §3 — interval base cases and full-interval count
-- statement:
--   Let n be even and x,y be n-bit vectors. For integer endpoints, the independent local semantic counts satisfy
--
--   $$j<i\ \Longrightarrow\ E_{i,j}=I_{i,j}=1,$$
--   $$0\le i\le j<n,\ j-i+1\text{ odd}\ \Longrightarrow\ E_{i,j}=I_{i,j}=0,$$
--   $$I_{0,n-1}=\#\{B:|B|=n/2,\ B\text{ is x-valid and y-eligible}\}.$$
--
--   These base values and the full-interval identity connect the local recurrence states to the exact output being computed. They are consequences of cardinality definitions, rather than recurrence definitions.
--
--   Differences from the source:
--   - reading: ways to match an interval using external or internal sets → E counts valid eligible local canonical matchings with every arrow forward; I counts all valid eligible local cyclic canonical matchings; reason: the global-leader reading contradicts E on the full two-point interval and I on the empty interval; the local reading preserves both displayed recurrences and the exact full count
--   - encoding: intervals [i,j], including j<i → integer endpoints with subintervals [i+1,k−1] and [k+1,j]; reason: negative endpoints represent the empty interval without truncated natural subtraction
--   - generalization: positive even cycle lengths → also the empty cycle n=0; reason: the unique half-subset is empty; its empty matching makes the geometric clauses vacuous and its polynomial and exact count equal one
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), §3 local-state prose and proof of Theorem 3.2, p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_IntervalCounts

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- §3 p.9: independent semantic counts have the stated empty/odd base values,
and on the full interval the internal state is the exact count. -/
theorem interval_base_cases (n : ℕ) (hn : Even n) (x y : Fin n → Bool) :
    (∀ i j : ℤ, j < i → extCount x y i j = 1 ∧ intCount x y i j = 1) ∧
    (∀ i j : ℤ, 0 ≤ i → i ≤ j → j < (n : ℤ) → Odd (j - i + 1) →
      extCount x y i j = 0 ∧ intCount x y i j = 0) ∧
    intCount x y 0 ((n : ℤ) - 1) = validEligibleCount n x y := by sorry

end ReadOnceParityBP.LowerBound
