-- Prove2me | Theorems.Thm_QiNonsmoothEq_Attraction_error_bound_5_5
-- name    : QiNonsmoothEq.Attraction.error_bound_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:21.642212+00:00
-- url     : https://prove2.me/theorems/a62adbc3-56a0-4642-aa79-d654e7b81af2
-- title:
--   Proof of Theorem 5.1, (5.3)–(5.5), p. 239 — near a B-differentiable zero x*, ‖x − x*‖ ≤ 2c‖F(x)‖
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and B-differentiable at a zero $x^*$ of $F$, and let $c$ be a constant with
--   $$\|h\|\le c\,\|F'(x^*;h)\|\quad\text{for all }h\in\mathbb R^n. \tag{5.3}$$
--   Then for every $\delta_1>0$ there is $\delta\in(0,\delta_1)$ such that every $x$ with $\|x-x^*\|\le\delta$ satisfies
--   $$\|x-x^*\|\ \le\ 2c\,\|F(x)\|. \tag{5.5}$$
--
--   This local error bound converts the residual $\|F(x)\|$ into a bound on the distance to $x^*$, with the explicit constant $2c$ tied to the $c$ of (5.3). It is the first step of the proof of the attraction theorem.
--
--   **Formalization Note** B-differentiability is assumed only at $x^*$, which is all the argument uses; Theorem 5.1 assumes it everywhere.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 239, proof of Theorem 5.1, (5.3)–(5.5)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, proof of Theorem 5.1, (5.3)–(5.5), p. 239: if `F` is B-differentiable at a zero
`x*` and `‖h‖ ≤ c ‖F'(x*; h)‖` for all `h` (5.3), then for every `δ₁ > 0` there is
`δ ∈ (0, δ₁)` with `‖y - x*‖ ≤ 2c ‖F(y)‖` whenever `‖y - x*‖ ≤ δ` (5.5). -/
theorem error_bound_5_5 {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖) :
    ∀ δ₁ : ℝ, 0 < δ₁ → ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧
      ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ → ‖y - xstar‖ ≤ 2 * c * ‖F y‖ := by sorry

end QiNonsmoothEq.Attraction
