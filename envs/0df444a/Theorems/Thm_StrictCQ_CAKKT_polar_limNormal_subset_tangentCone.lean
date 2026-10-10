-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_polar_limNormal_subset_tangentCone
-- name    : StrictCQ.CAKKT.polar_limNormal_subset_tangentCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:14.137987+00:00
-- url     : https://prove2.me/theorems/319e2477-c30e-46cc-bb58-e5d35901ceee
-- title:
--   proof of Theorem 6.4, p. 24 — for closed S, N_S(z)° ⊂ T_S(z) (Rockafellar–Wets 6.28(b), 6.26)
-- statement:
--   For every closed set $S\subseteq\mathbb R^n$ and every $z\in S$, the polar of the limiting normal cone is contained in the tangent cone:
--   $$N_S(z)^\circ\subseteq T_S(z).$$
--
--   The paper cites Rockafellar–Wets, Theorems 6.28(b) and 6.26: the polar of the limiting normal cone of a closed set is its regular (Clarke) tangent cone, and the regular tangent cone is contained in the tangent cone. In the proof of Theorem 6.4 it is applied to $S=\Omega$, which is closed because the constraint functions are continuous.
--
--   **Formalization Note** The statement is for an arbitrary closed set; closedness is the hypothesis of Rockafellar–Wets 6.28.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 24, proof of Theorem 6.4 (citing Rockafellar–Wets, Theorems 6.28(b) and 6.26)

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem polar_limNormal_subset_tangentCone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsClosed S) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ S) :
    StrictCQ.AGP.polar (limNormal S z) ⊆ tangentCone S z := by sorry
end StrictCQ.CAKKT
