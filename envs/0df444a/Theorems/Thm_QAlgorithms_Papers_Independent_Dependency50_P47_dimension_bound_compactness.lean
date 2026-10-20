-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_dimension_bound_compactness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.dimension_bound_compactness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:37:54.930197+00:00
-- url     : https://prove2.me/theorems/19a7ba11-ece9-4110-a441-2bf6e2247aad
-- title:
--   Remark 1: conditional compactness consequence of a dimension bound
-- statement:
--   Fix the finite law $p(a,b,x,y)$ and the rate regions $\mathcal S_\epsilon,\mathcal R^q$ of Theorem 2. Suppose there is one positive integer $D$, chosen before the error tolerance and rate, such that every rate in every $\mathcal S_\epsilon$ with $\epsilon>0$ has a witness with $1\le\dim F\le D$. Then
--
--   $$
--   \mathcal S_0=\bigcap_{\epsilon>0}\mathcal S_\epsilon=\mathcal R^q.
--   $$
--
--   This is the conditional compactness consequence of a uniform auxiliary dimension bound. It does not assert the existence of that bound.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 8, Remark 1: conditional compactness consequence of a dimension bound

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Remark 1, PDF p.8: only a conditional equality. The dimension bound is chosen before
both epsilon and rate, so zero-padding and compactness apply uniformly. -/
theorem dimension_bound_compactness {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (p : Law (Fin a × Fin b × Fin x × Fin y))
    (hbound : ∃ D : ℕ, 0 < D ∧ ∀ eps : ℝ, 0 < eps →
      singleLetterRegion p eps ⊆ boundedSingleLetterRegion p eps D) :
    singleLetterRegion p 0 = {R | ∀ eps : ℝ, 0 < eps → R ∈ singleLetterRegion p eps} ∧
      singleLetterRegion p 0 = quantumRates p := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
