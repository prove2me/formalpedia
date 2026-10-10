-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_regNormal_eq_polar_tangentCone
-- name    : StrictCQ.CAKKT.regNormal_eq_polar_tangentCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:02.703853+00:00
-- url     : https://prove2.me/theorems/de49ee0d-eacc-4c35-8c1e-5421c3815986
-- title:
--   proof of Theorem 6.4, p. 23 — the regular normal cone is the polar of the tangent cone: N̂_S(z) = T_S(z)°
-- statement:
--   For every set $S\subseteq\mathbb R^n$ and every $z\in S$,
--   $$\widehat N_S(z)=T_S(z)^\circ,$$
--   where $\widehat N_S(z)$ is the regular (Fréchet) normal cone (3.4), $T_S(z)$ the tangent cone (3.3) and ${}^\circ$ the polar.
--
--   The paper uses this identity, with $S=\Omega$, in the proof of Theorem 6.4 without citation; it is Rockafellar–Wets, Proposition 6.5. It lets regular normals be produced from polar tangent vectors, which is where Lemma 6.2 applies.
--
--   **Formalization Note** No closedness is needed. The hypothesis $z\in S$ is required because the regular normal cone is empty off $S$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 23, proof of Theorem 6.4 ("y^k ∈ N̂_Ω(x^k) = T°_Ω(x^k)")

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem regNormal_eq_polar_tangentCone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ S) :
    regNormal S z = StrictCQ.AGP.polar (tangentCone S z) := by sorry
end StrictCQ.CAKKT
