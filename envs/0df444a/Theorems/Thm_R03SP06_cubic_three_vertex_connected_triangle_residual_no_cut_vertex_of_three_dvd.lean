-- Prove2me | Theorems.Thm_R03SP06_cubic_three_vertex_connected_triangle_residual_no_cut_vertex_of_three_dvd
-- name    : R03SP06.cubic_three_vertex_connected_triangle_residual_no_cut_vertex_of_three_dvd
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:36.740183+00:00
-- url     : https://prove2.me/theorems/1f41511c-ee06-46b1-a840-fa32dd4079db
-- title:
--   Cubic three vertex connected triangle residual no cut vertex of three dvd
-- statement:
--   Direct root-domain structural corollary for triangle deletions. This is still only a connectivity reduction: it does not provide a P3-factor for the residual.
--
--   $$G-V(C_3)\text{ satisfies the stated residual-connectivity conclusion}.$ $
--
--   This isolates one reusable port-counting or residual-connectivity step for deleting a triangle from a cubic three-vertex-connected graph. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cubic_three_vertex_connected_triangle_residual_no_cut_vertex_of_three_dvd
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    {a b c x : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by sorry

end R03SP06
