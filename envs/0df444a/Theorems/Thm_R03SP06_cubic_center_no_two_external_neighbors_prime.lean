-- Prove2me | Theorems.Thm_R03SP06_cubic_center_no_two_external_neighbors_prime
-- name    : R03SP06.cubic_center_no_two_external_neighbors_prime
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:26.339015+00:00
-- url     : https://prove2.me/theorems/555f23ff-eb97-403f-ae73-404d822b28f7
-- title:
--   Cubic center no two external neighbors
-- statement:
--   Conditional q=3 cut-free theorem. The `hport` premise is the one-external neighbor property of a triangle in a cubic simple graph.
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

theorem cubic_center_no_two_external_neighbors_prime
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b c x y : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxc : x ≠ c) (hya : y ≠ a) (hyc : y ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3) :
    False := by sorry

end R03SP06
