-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_eq_2_11
-- name    : PrimalDualSubgrad.DA.eq_2_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:59.582992+00:00
-- url     : https://prove2.me/theorems/6432003b-137e-4fd4-9792-09c06c9b0e1f
-- title:
--   (2.11) — δ_k(D) = Σλᵢ⟨gᵢ, xᵢ − x₀⟩ + ξ_D(−s_{k+1})
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$ and arbitrary sequences $x_i \in E$, $g_i \in E^*$, $\lambda_i \in \mathbb{R}$. For every $k \ge 0$ and $D \ge 0$, with $s_{k+1} = \sum_{i=0}^k \lambda_i g_i$,
--   $$\delta_k(D) = \sum_{i=0}^k \lambda_i\langle g_i, x_i - x_0\rangle + \xi_D(-s_{k+1}).$$
--
--   This is the explicit representation of the gap function through the support function of $F_D$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §2, (2.11), p. 8

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_DualAveraging

namespace PrimalDualSubgrad.DA

open Finset

/-- (2.11), p. 8: for any sequences `x_i ∈ E`, `g_i ∈ E*`, `λ_i ∈ ℝ` and `D ≥ 0`,
`δ_k(D) = ∑_{i=0}^k λ_i⟨g_i, x_i − x0⟩ + ξ_D(−s_{k+1})`. -/
theorem eq_2_11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (lam : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    delta P lam g x k D =
      ∑ i ∈ range (k + 1), lam i * g i (x i - P.x0) + xi P D (-(sAgg lam g (k + 1))) := by sorry

end PrimalDualSubgrad.DA
