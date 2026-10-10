-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_limNormal_subset_polar_linCone
-- name    : StrictCQ.CAKKT.limNormal_subset_polar_linCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:22.829073+00:00
-- url     : https://prove2.me/theorems/30236e3a-c99f-47c2-ab7b-c37af713f10c
-- title:
--   proof of Theorem 6.4, pp. 23–24 — under CAKKT-regularity, N_Ω(x*) ⊂ L_Ω(x*)°
-- statement:
--   Let $h_i,g_j$ be continuously differentiable and let $x^*\in\Omega$ be CAKKT-regular. Then the limiting normal cone (3.5) of $\Omega$ at $x^*$ is contained in the polar of the linearized cone:
--   $$N_\Omega(x^*)\subseteq L_\Omega(x^*)^\circ.$$
--
--   This is the core step of Theorem 6.4: it is where CAKKT-regularity enters, and with $N_\Omega(x^*)^\circ\subseteq T_\Omega(x^*)$ it yields Abadie's constraint qualification.
--
--   **Formalization Note** $N_\Omega$ is the limiting (Mordukhovich) normal cone of the possibly nonconvex $\Omega$, not the normal cone of convex analysis.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 23–24, proof of Theorem 6.4

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem limNormal_subset_polar_linCone {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) (hreg : C.CAKKTRegular xs) :
    limNormal C.feasible xs ⊆ StrictCQ.AGP.polar (C.linCone xs) := by sorry
end StrictCQ.CAKKT
