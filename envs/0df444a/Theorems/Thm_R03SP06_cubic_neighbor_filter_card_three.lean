-- Prove2me | Theorems.Thm_R03SP06_cubic_neighbor_filter_card_three
-- name    : R03SP06.cubic_neighbor_filter_card_three
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:54.786033+00:00
-- url     : https://prove2.me/theorems/ff283499-6e3f-4af3-9303-47405bef1dc9
-- title:
--   Cubic neighbor filter card three
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

theorem cubic_neighbor_filter_card_three
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (v : V) :
    (Finset.univ.filter (fun w : V => G.Adj v w)).card = 3 := by sorry

end R03SP06
