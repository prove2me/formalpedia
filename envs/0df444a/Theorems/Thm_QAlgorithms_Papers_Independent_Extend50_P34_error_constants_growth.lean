-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_error_constants_growth
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.error_constants_growth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:12:51.008574+00:00
-- url     : https://prove2.me/theorems/1544ed15-8d4a-4ae3-851f-33ffec81275a
-- title:
--   Lemma 5.8
-- statement:
--   The constants in Lemma 5.7 can be chosen jointly with an absolute $b>0$ so that
--
--   $$A_C\le2^{bC^2\log C}\qquad(C\ge2).$$
--
--   Moreover the finite rational coefficients in the central-character expansion of $O_k$ can be chosen with $\sum_\mu|c_{k,\mu}|\le2^{bk^2\log k}$ for $k\ge2$, as proved in equation (41). These choices satisfy the error bound simultaneously for all $r,n,\omega$ in the standing regime. This makes the degree dependence quantitative.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 50, Lemma 5.8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.8, arXiv:1501.05028v1, PDF p.50. Existentially choose the witnesses jointly: an arbitrary oversized witness A_C need not obey the bound. Visually verified C² log C. -/
theorem error_constants_growth
    : ∃ (A : ℕ → ℝ) (b : ℝ), 0 < b ∧ ErrorConstants A ∧
      (∀ C : ℕ, 2 ≤ C → A C ≤ Real.rpow 2 (b*C^2*Real.log C)) ∧
      (∀ k : ℕ, 2 ≤ k → ∃ a : YoungDiagram →₀ ℚ,
        (∀ mu ∈ a.support, observableWeight mu ≤ k) ∧
        (∀ lambda, remainder k lambda = observable a lambda) ∧
        (∑ mu ∈ a.support, |(a mu : ℝ)|) ≤ Real.rpow 2 (b*k^2*Real.log k)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
