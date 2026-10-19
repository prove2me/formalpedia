-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_psd_cubic_rays
-- name    : QAlgorithms.Papers.Independent.Information100.P19.psd_cubic_rays
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:45:24.406298+00:00
-- url     : https://prove2.me/theorems/ead7d0c5-96e6-4062-afce-4a6befcbaaf7
-- title:
--   Proposition 3.5
-- statement:
--   The extremal rays of the dimension-free PSD cubic cone are exactly
--   $$\mathbb R_{\ge0}[3],\quad \mathbb R_{\ge0}([21]-[3]),\quad
--   \mathbb R_{\ge0}([1^3]-(2k+1)[21]+k(k+1)[3]),\quad k\ge1.$$
--   The cone is nonpolyhedral. These are linear homogeneous inequalities, rather than the nonlinear spectral-bound curve.
--
--   For a partition $\lambda$, the symbol $[\lambda]$ denotes a formal basis element evaluated as $\prod_j\operatorname{Tr}(X^{\lambda_j})$. Distinct formal coefficients are not identified by any fixed-dimensional trace identity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 13, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 3.5; arXiv:2609.29471v1, PDF pp.13, 14, 15, 16. -/
theorem psd_cubic_rays  :
    extremeRays (psdCone 3) =
      ({ray b3,ray (b21-b3)} ∪ {R | ∃ k : ℕ, 1 ≤ k ∧ R = ray (cubicRay k)}) ∧
    ¬ IsPolyhedral (psdCone 3) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
