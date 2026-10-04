-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_gTilde_ne_zero
-- name    : ShorNonsmooth.SpaceDilation.sdg_gTilde_ne_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:12:05.630502+00:00
-- url     : https://prove2.me/theorems/687e893c-0d7a-47d6-8e7f-197fb6aa9bbd
-- title:
--   Transformed gradients are nonzero along a non-stopped SDG run
-- statement:
--   If the SDG method never triggers its stopping rule through step $k$ (with coefficients bounded away from zero), the transformed gradient $\tilde g_k = B_k^* g(x_k)$ is nonzero: each $B_j$ is a composition of surjective operators, so $B_j^*$ is injective. Hence every dilation direction in the run is a genuine unit vector.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, formulas (3.6)-(3.7), pp. 51-52: the normalized transformed gradient xi_{k+1} requires gTilde_k nonzero.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Since each `B_j` is a composition of the nonsingular `B_0` with invertible dilations `R_{1/α_i}(ξ_i)` (unit directions, nonzero coefficients), `B_j` is surjective, so its adjoint is injective: `g(x_j) ≠ 0` implies `g̃_j = B_j^* g(x_j) ≠ 0`. Hence every normalized direction `ξ_{j+1} = g̃_j / ‖g̃_j‖` in Theorem 3.1 is a genuine unit vector. -/
theorem sdg_gTilde_ne_zero {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j ≤ k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    gTilde g h α x₀ B₀ k ≠ 0 := by sorry

end ShorNonsmooth.SpaceDilation
