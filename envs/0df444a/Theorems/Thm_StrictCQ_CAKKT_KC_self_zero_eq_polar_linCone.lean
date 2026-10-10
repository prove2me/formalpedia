-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_KC_self_zero_eq_polar_linCone
-- name    : StrictCQ.CAKKT.KC_self_zero_eq_polar_linCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:09.783099+00:00
-- url     : https://prove2.me/theorems/00c296b4-88f7-4eda-92ac-5b6ddc412931
-- title:
--   p. 9, after (4.16) — K_C(x*, 0) coincides with L_Ω(x*)°
-- statement:
--   Let $x^*$ be feasible for (1.1). Then
--   $$K_C(x^*,0)=L_\Omega(x^*)^\circ,$$
--   that is, the set of combinations $\sum_i\lambda_i\nabla h_i(x^*)+\sum_{j\in J(x^*)}\mu_j\nabla g_j(x^*)$ with $\mu\ge 0$ (the complementarity bound is automatic at the feasible point) is exactly the polar of the linearized cone.
--
--   This identifies the right-hand side of (4.17) with the polar of the linearized cone, so that CAKKT-regularity is a perturbation of the classical description of $L_\Omega(x^*)^\circ$; it is used in Theorem 4.3 and in the proof of Theorem 6.4.
--
--   **Formalization Note** No differentiability hypothesis is needed: the identity is a Farkas-type statement about the finitely many vectors $\nabla h_i(x^*)$, $\nabla g_j(x^*)$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 9, after (4.16) and in (4.17)

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem KC_self_zero_eq_polar_linCone {n m p : ℕ} (C : Constraints n m p)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) :
    C.KC xs xs 0 = StrictCQ.AGP.polar (C.linCone xs) := by sorry
end StrictCQ.CAKKT
