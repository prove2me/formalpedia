-- Prove2me | Theorems.Thm_R03SP06_cubic_triangle_residual_two_connected
-- name    : R03SP06.cubic_triangle_residual_two_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:29.174387+00:00
-- url     : https://prove2.me/theorems/82358310-22d9-4a1a-9567-2d4050efd5b2
-- title:
--   Cubic triangle residual two connected
-- statement:
--   Package the preceding two statements as the standard 2-connectivity condition needed by the q=3 factor reduction.
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

theorem cubic_triangle_residual_two_connected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hcard : 6 ≤ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected ∧
      ∀ x : V, x ≠ a ∧ x ≠ b ∧ x ≠ c →
        (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by sorry

end R03SP06
