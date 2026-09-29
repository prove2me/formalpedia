-- Prove2me | Theorems.Thm_R03SP06_closed_side_induced_not_connected
-- name    : R03SP06.closed_side_induced_not_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:44.109951+00:00
-- url     : https://prove2.me/theorems/c8ed7dd1-8f90-41ce-9bfd-c09a58f26ff3
-- title:
--   Closed side induced not connected
-- statement:
--   Reusable auxiliary theorem closed_side_induced_not_connected from the verified P3-factor development.
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

theorem closed_side_induced_not_connected
    {G : SimpleGraph V} {A B S : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ S) :
    ¬ (G.induce {v : V | v ∉ S}).Connected := by sorry

end R03SP06
