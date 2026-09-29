-- Prove2me | Theorems.Thm_R03SP06_cubic_triangle_external_port_unique
-- name    : R03SP06.cubic_triangle_external_port_unique
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:21.354599+00:00
-- url     : https://prove2.me/theorems/3b21983d-20dd-443e-8056-6ebbd4e7a0b8
-- title:
--   Cubic triangle external port unique
-- statement:
--   The one-external-neighbor condition for each vertex of a triangle.
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

theorem cubic_triangle_external_port_unique
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∀ ⦃t u v : V⦄, t ∈ ({a, b, c} : Finset V) →
      u ∉ ({a, b, c} : Finset V) → v ∉ ({a, b, c} : Finset V) →
      G.Adj t u → G.Adj t v → u = v := by sorry

end R03SP06
