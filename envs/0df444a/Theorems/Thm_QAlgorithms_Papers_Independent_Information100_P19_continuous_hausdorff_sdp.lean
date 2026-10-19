-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_continuous_hausdorff_sdp
-- name    : QAlgorithms.Papers.Independent.Information100.P19.continuous_hausdorff_sdp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:55:52.001292+00:00
-- url     : https://prove2.me/theorems/b8c3ea18-d11e-4fec-946a-4330764567f6
-- title:
--   §5.1 unnumbered: continuous relaxation and Hausdorff SDP
-- statement:
--   For nonnegative prescribed even moments $r_1,\ldots,r_m$, $m\ge1$, relax unit atoms to arbitrary finite nonnegative measures supported on $[0,1]$, with free total mass. Then
--   $$\alpha_c(r)\le\alpha(r),\qquad
--   \alpha_c(r)=\inf\{y_1:(y_{i+j})_{i,j=0}^{m}\succeq0,\ (y_{i+j+1}-y_{i+j+2})_{i,j=0}^{m-1}\succeq0,\ y_{2k}=r_k\}.$$
--   A nonnegative truncated sequence has a representing finite measure exactly when those two matrices are PSD. Their sizes are $m+1$ and $m$, and infeasible optima have value $+\infty$. This is the source's Hausdorff SDP representation, with no integer-mass or rank constraint.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 32, §5.1 unnumbered: continuous relaxation and Hausdorff SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §5.1 unnumbered: continuous relaxation and Hausdorff SDP; arXiv:2609.29471v1, PDF pp.32, 33. -/
theorem continuous_hausdorff_sdp (m : ℕ) (hm : 1 ≤ m) (r : Fin m → ℝ) (hr : ∀ k, 0≤r k) :
    alphaC r ≤ alpha r ∧ alphaC r = sdpValue r ∧
    (∀ y : ℕ → ℝ, (∀ j≤2*m, 0≤y j) →
      ((∃ μ : Measure ℝ, μ Set.univ < ∞ ∧ μ (Set.Icc (0:ℝ) 1)ᶜ=0 ∧
        ∀ j≤2*m, Integrable (fun x : ℝ => x^j) μ ∧ (∫ x, x^j ∂μ)=y j) ↔
      (Matrix.of (fun i j : Fin (m+1) => y (i.val+j.val))).PosSemidef ∧
      (Matrix.of (fun i j : Fin m => y (i.val+j.val+1)-y (i.val+j.val+2))).PosSemidef)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
