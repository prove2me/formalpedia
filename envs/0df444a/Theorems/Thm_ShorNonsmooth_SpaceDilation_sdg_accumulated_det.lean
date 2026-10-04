-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_accumulated_det
-- name    : ShorNonsmooth.SpaceDilation.sdg_accumulated_det
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:20.920466+00:00
-- url     : https://prove2.me/theorems/16198b38-526e-46c3-8f13-70cbe809111f
-- title:
--   Accumulated SDG transformation has determinant prod alpha_j times det A_0
-- statement:
--   Run the SDG method from $x_0$ with nonsingular $B_0 = A_0^{-1}$ and coefficients $\alpha_j \ge 1+\delta$. If the stopping rule $g(x_j) = 0$ never triggers before step $k$, the accumulated transformation satisfies $\det A_k = (\prod_{j=1}^k \alpha_j)\det A_0$. The non-stopping hypothesis is needed because a stopped state freezes while the coefficient product keeps growing.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, proof of Theorem 3.1, p. 53: A_k is the product of the dilation operators R_{alpha_j}(xi_j) applied to A_0.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), proof of Theorem 3.1, p. 53: along an SDG run that never triggers the stopping rule, `A_k = R_{α_k}(ξ_k) ⋯ R_{α_1}(ξ_1) A_0`, hence `det A_k = (∏_{j=1}^k α_j) det A_0`. When `g(x_j) = 0` the state freezes while the product keeps growing, so the non-stopping hypothesis is required. -/
theorem sdg_accumulated_det {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    LinearMap.det (sdg g h α x₀ B₀ k).A.toLinearMap =
      (∏ j ∈ Finset.Icc 1 k, α j) *
        LinearMap.det (B₀.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap := by sorry

end ShorNonsmooth.SpaceDilation
