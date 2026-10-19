-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_moment_threshold_realization
-- name    : QAlgorithms.Papers.Independent.Information100.P19.moment_threshold_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:09.942472+00:00
-- url     : https://prove2.me/theorems/21d8a5c9-0f1d-45cd-96df-089dda16b71f
-- title:
--   Introduction: optimality of the moment threshold in Proposition 5.12
-- statement:
--   For every positive number M of prescribed even moments, let r=(r_1,...,r_M) be nonnegative with r_1≤1, and let alpha(r) be the extended nonnegative infimum in Eq.(17). Then alpha(r)≤1 if and only if there is a finite vector s with entries in [0,1], sum_i s_i^(2k)=r_k for every k=1,...,M, and sum_i s_i≤1. Thus the moments are compatible with the scalar realignment norm bound exactly when this threshold test accepts. This asserts scalar spectral compatibility, not the existence of a separable matrix.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 6, Introduction, main result (3), converse optimality assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Introduction p.6: optimality of the threshold test in Proposition 5.12.
The source says that alpha(r) <= 1 is realized by a finite nonnegative vector
of l1 norm at most one. This is the threshold-attainment assertion, beyond
merely taking the infimum in Eq.(17); it does not assert a separable realization. -/
theorem moment_threshold_realization (m : ℕ) (r : Fin (m+1) → ℝ)
    (hr : ∀ k, 0 ≤ r k) (hbound : r 0 ≤ 1) :
    alpha r ≤ 1 ↔ ∃ N : ℕ, ∃ s : Fin N → ℝ,
      discreteFeasible r s ∧ (∑ i, s i) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
