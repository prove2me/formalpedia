-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_theorem_6_4
-- name    : StrictCQ.CAKKT.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:20.251759+00:00
-- url     : https://prove2.me/theorems/93a06825-3477-4db7-81f1-f2dfba148987
-- title:
--   Theorem 6.4, p. 23 — CAKKT-regularity implies Abadie's constraint qualification
-- statement:
--   Let $h_1,\dots,h_m,g_1,\dots,g_p:\mathbb R^n\to\mathbb R$ be continuously differentiable, $\Omega=\{x: h(x)=0,\ g(x)\le 0\}$, and let $x^*\in\Omega$ be CAKKT-regular (Definition 4.2). Then Abadie's constraint qualification holds at $x^*$:
--   $$L_\Omega(x^*)=T_\Omega(x^*),$$
--   where $L_\Omega(x^*)$ is the linearized cone (3.7) and $T_\Omega(x^*)$ the tangent cone (3.3).
--
--   Together with Example 6.1 of the paper, this shows that CAKKT-regularity is strictly stronger than Abadie's CQ, placing the weakest strict constraint qualification for CAKKT within the classical hierarchy of constraint qualifications.
--
--   **Formalization Note** Abadie's CQ is the equality of cones of p. 5, not the equality of their polars (that would be Guignard's CQ (3.8)). The proof's opening sentence writes "$T_\Omega(x^*)=L_\Omega(x^*)^\circ$", a misprint. Closedness of $\Omega$ is not assumed; it follows from continuity of the constraints.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 23, Theorem 6.4

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem theorem_6_4 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) (hreg : C.CAKKTRegular xs) :
    C.Abadie xs := by sorry
end StrictCQ.CAKKT
