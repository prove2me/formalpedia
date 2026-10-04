-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_B_comp_A
-- name    : ShorNonsmooth.SpaceDilation.sdg_B_comp_A
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:55.776564+00:00
-- url     : https://prove2.me/theorems/740b33d0-ad97-476d-a9d9-6c98a23d5785
-- title:
--   SDG operators satisfy B_k A_k = id along a non-stopped run
-- statement:
--   Along an SDG run that never stops ($g(x_j) \ne 0$ for $j < k$), with coefficients $\alpha_j \ge 1+\delta > 0$, the operators satisfy $B_k A_k = I$: each dilation $R_{1/\alpha}(\xi)$ cancels the matching $R_\alpha(\xi)$ since $\xi$ is a unit vector. In particular $B_k = A_k^{-1}$ at every non-stopped step.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, formulas (3.8)-(3.9), pp. 51-52: B_k and A_k are maintained as mutual inverses through the dilation updates.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), formulas (3.9), pp. 51-52: since `B_{k+1} = B_k R_{1/α_{k+1}}(ξ_{k+1})`, `A_{k+1} = R_{α_{k+1}}(ξ_{k+1}) A_k` and `R_{1/α}(ξ) ∘ R_α(ξ) = id` for a unit vector `ξ` and nonzero `α`, induction maintains `B_k ∘ A_k = id` along runs that never trigger the stopping rule. Hence `B_k = A_k^{-1}` and `A_k^* ξ_{k+1} = g(x_k) / ‖g̃_k‖`. -/
theorem sdg_B_comp_A {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    ((sdg g h α x₀ B₀ k).B.toLinearMap).comp ((sdg g h α x₀ B₀ k).A.toLinearMap) =
      LinearMap.id := by sorry

end ShorNonsmooth.SpaceDilation
