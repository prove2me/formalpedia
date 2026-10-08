-- Prove2me | Theorems.Thm_QiNonsmoothEq_Local_corollary_3_2
-- name    : QiNonsmoothEq.Local.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:50.813305+00:00
-- url     : https://prove2.me/theorems/fb9647f4-08e8-4a9d-860c-341e6f769de3
-- title:
--   Corollary 3.2, p. 235 — near a semismooth, strongly BD-regular zero one ∂_B Newton step contracts ‖x − x*‖ and ‖F‖ by any factor ε
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz, let $x^*$ be a zero of $F$, and let $F$ be semismooth and strongly BD-regular at $x^*$. Then for every $\varepsilon>0$ there is $\delta>0$ such that for every $x$ with $\|x-x^*\|\le\delta$ and every $V\in\partial_B F(x)$, the map $V$ is nonsingular and
--   $$\|x-V^{-1}F(x)-x^*\|\le\varepsilon\|x-x^*\|,\qquad \|F(x-V^{-1}F(x))\|\le\varepsilon\|F(x)\|.$$
--
--   The corollary isolates the one-step estimates behind Theorem 3.1: a single $\partial_B$ Newton step from close to $x^*$ shrinks both the distance to the zero and the residual by an arbitrarily small factor. It is reused for the damped Newton method in §4.
--
--   **Formalization Note** The paper prints "for any $\varepsilon\ge 0$"; for $\varepsilon=0$ the claim would force exact convergence in one step, which fails in general, so the statement is made for $\varepsilon>0$. $V^{-1}$ is written as any two-sided inverse $W$ of $V$ (it is unique). Local Lipschitz continuity of $F$ is the paper's standing assumption (§1).
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 235, Corollary 3.2

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), Corollary 3.2, p. 235. Let `x*` be a zero of `F`, and let `F` be semismooth and
strongly BD-regular at `x*`. For every `ε > 0` (the page prints `ε ≥ 0`) there is `δ > 0` such that
for every `x` with `‖x - x*‖ ≤ δ` and every `V ∈ ∂_B F(x)`, `V` is nonsingular and
`‖x - V⁻¹F(x) - x*‖ ≤ ε ‖x - x*‖`, `‖F(x - V⁻¹F(x))‖ ≤ ε ‖F(x)‖`. -/
theorem corollary_3_2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (xstar : EuclideanSpace ℝ (Fin n)) (hzero : F xstar = 0)
    (hss : NonsmoothNewton.Local.SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ →
      ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        (∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W) ∧
        ∀ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W →
          ‖y - W (F y) - xstar‖ ≤ ε * ‖y - xstar‖ ∧
          ‖F (y - W (F y))‖ ≤ ε * ‖F y‖ := by sorry

end QiNonsmoothEq.Local
