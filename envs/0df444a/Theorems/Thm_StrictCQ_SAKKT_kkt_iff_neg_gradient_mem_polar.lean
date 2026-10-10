-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_kkt_iff_neg_gradient_mem_polar
-- name    : StrictCQ.SAKKT.kkt_iff_neg_gradient_mem_polar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:54.288139+00:00
-- url     : https://prove2.me/theorems/cbc8597d-f803-44fe-9359-c04c1c24f4e4
-- title:
--   (4.25), proof of Theorem 4.5, p. 12 — KKT holds at x* iff −∇f(x*) ∈ L_Ω(x*)°
-- statement:
--   Let $x^*$ be a feasible point of (1.1) and $f$ an objective. Then
--   $$-\nabla f(x^*)\in L_\Omega(x^*)^\circ\iff \text{the KKT condition holds at } x^* \text{ for } f,$$
--   where $L_\Omega(x^*)$ is the linearized cone (3.7) and $K^\circ$ is the polar cone.
--
--   This identifies the geometric form of KKT used throughout the paper with the multiplier form: it is the step "proving that $x^*$ satisfies the KKT condition" after (4.25).
--
--   **Formalization Note** KKT is the multiplier form: $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p_+$ with $\mu_j=0$ for every inactive $j$, and $\nabla f(x^*)+\sum\lambda_i\nabla h_i(x^*)+\sum\mu_j\nabla g_j(x^*)=0$. No differentiability of $f$ or the constraints is assumed: only the gradient vectors at $x^*$ enter.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 12, (4.25) and proof of Theorem 4.5

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- Proof of Theorem 4.5, p. 12: at a feasible `xs`, KKT holds for `f` iff `-∇f(xs) ∈ L_Ω(xs)°`. -/
theorem kkt_iff_neg_gradient_mem_polar {n m p : ℕ} (C : Constraints n m p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n))
    (hxs : xs ∈ C.feasible) :
    -gradient f xs ∈ StrictCQ.AGP.polar (C.linCone xs) ↔ C.IsKKT f xs := by sorry

end StrictCQ.SAKKT
