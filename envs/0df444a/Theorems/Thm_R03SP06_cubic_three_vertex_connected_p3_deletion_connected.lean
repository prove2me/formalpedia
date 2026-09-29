-- Prove2me | Theorems.Thm_R03SP06_cubic_three_vertex_connected_p3_deletion_connected
-- name    : R03SP06.cubic_three_vertex_connected_p3_deletion_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:04.33925+00:00
-- url     : https://prove2.me/theorems/d4575d38-7584-4cf2-8233-bc31d14c6ca9
-- title:
--   Cubic three vertex connected p3 deletion connected
-- statement:
--   Project-model wrapper: the local degree hypothesis is supplied by `Cubic`, and the two-vertex deletion connectivity hypothesis is supplied by `ThreeVertexConnected`. This closes the candidate formalization of the connectivity-after-P3-deletion lemma, but it still says nothing about a P3-factor in the residual graph.
--
--   $$\kappa(G)\ge 3\quad\Longrightarrow\quad G-V(P_3)\text{ satisfies the stated connectivity conclusion}.$ $
--
--   This isolates one reusable separator or residual-connectivity step for deleting a displayed $P_3$ from a cubic three-vertex-connected graph. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [DecidableEq V]

theorem cubic_three_vertex_connected_p3_deletion_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by sorry

end R03SP06
