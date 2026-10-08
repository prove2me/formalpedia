-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_eq_2_13
-- name    : PrimalDualSubgrad.DA.eq_2_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:03.231999+00:00
-- url     : https://prove2.me/theorems/9c59f45f-cfe8-4ecf-8c44-5ff645899534
-- title:
--   (2.13) — δ_k(D) ≤ Δ_k(β, D)
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$ and arbitrary sequences $x_i \in E$, $g_i \in E^*$, $\lambda_i \in \mathbb{R}$. For every $k \ge 0$, $D \ge 0$ and $\beta > 0$,
--   $$\delta_k(D) \le \Delta_k(\beta, D).$$
--
--   The gap is thus controlled by the upper gap function, which is what Theorem 1 bounds along the scheme.
--
--   **Formalization Note** The page says "for any non-negative $D$ and $\beta$"; $V_\beta$, and so $\Delta_k(\beta, D)$, is defined only for $\beta > 0$. The page considers $x_i \in Q$ and $\lambda_i \ge 0$; the statement holds, and is stated, for arbitrary sequences.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §2, (2.13), p. 9

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_DualAveraging

namespace PrimalDualSubgrad.DA

/-- (2.13), p. 9: for any sequences `x_i ∈ E`, `g_i ∈ E*`, `λ_i ∈ ℝ`, any `D ≥ 0` and
`β > 0`, `δ_k(D) ≤ Δ_k(β, D)`. (The page says "non-negative β"; `V_0` is undefined.) -/
theorem eq_2_13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (lam : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (k : ℕ) (β D : ℝ) (hβ : 0 < β) (hD : 0 ≤ D) :
    delta P lam g x k D ≤ Delta P lam g x k β D := by sorry

end PrimalDualSubgrad.DA
