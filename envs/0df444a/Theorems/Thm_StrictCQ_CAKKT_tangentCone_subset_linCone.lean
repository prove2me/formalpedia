-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_tangentCone_subset_linCone
-- name    : StrictCQ.CAKKT.tangentCone_subset_linCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:11.371371+00:00
-- url     : https://prove2.me/theorems/f448cd8f-1417-4f60-902b-c2326d53c32e
-- title:
--   proof of Theorem 6.4, p. 23 — the tangent cone is contained in the linearized cone: T_Ω(x*) ⊂ L_Ω(x*)
-- statement:
--   Let $h_i,g_j$ be continuously differentiable and $x^*\in\Omega$. Then
--   $$T_\Omega(x^*)\subseteq L_\Omega(x^*),$$
--   where $T_\Omega$ is the tangent cone (3.3) and $L_\Omega$ the linearized cone (3.7).
--
--   This is the inclusion that always holds; Abadie's constraint qualification asks for the reverse one. The proof of Theorem 6.4 states it as "$T_\Omega(x^*)\subset L_\Omega(x^*)^\circ$ always holds".
--
--   **Formalization Note** The page writes $T_\Omega(x^*)\subset L_\Omega(x^*)^\circ$ and describes Abadie's CQ as $T_\Omega(x^*)=L_\Omega(x^*)^\circ$; the polars are misprints, since p. 5 defines Abadie's CQ as $L_\Omega(x^*)=T_\Omega(x^*)$ and the inclusion between tangent and polar-linearized cones is false in general. The statement here is the true inclusion of the cones of p. 5.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 23, proof of Theorem 6.4, first sentence

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem tangentCone_subset_linCone {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) :
    tangentCone C.feasible xs ⊆ C.linCone xs := by sorry
end StrictCQ.CAKKT
