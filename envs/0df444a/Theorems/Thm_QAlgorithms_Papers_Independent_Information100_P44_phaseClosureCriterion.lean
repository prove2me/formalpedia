-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_phaseClosureCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P44.phaseClosureCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:37:27.674277+00:00
-- url     : https://prove2.me/theorems/2774828b-83f6-4f42-981f-3d442ae33c95
-- title:
--   Lemma 2: exact phase-closure criterion
-- statement:
--   Let $n\ge1$ and let $a_1,\ldots,a_n$ be nonnegative real numbers. Then
--   $$\bigl(\exists z_1,\ldots,z_n\in\mathbb C:\ |z_k|=a_k\text{ for all }k,\ \sum_kz_k=0\bigr)\quad\Longleftrightarrow\quad\forall k,\ a_k\le\sum_{j\ne k}a_j.$$
--   The right side is equivalent to $2\max_k a_k\le\sum_k a_k$. For $n=1$ it forces the sole length to be zero, and the all-zero family is allowed. This is phase closure alone and does not ensure CP or thermal realizability.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 12, Lemma 2: exact phase-closure criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.12–13, Lemma 2: max-free equivalent of 2 max a <= sum a, on a nonempty family. -/
theorem phaseClosureCriterion {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    (∃ z : Fin n → ℂ, (∀ k, ‖z k‖ = a k) ∧ ∑ k, z k = 0) ↔
      ∀ k, a k ≤ ∑ j ∈ Finset.univ.erase k, a j := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
