-- Prove2me | Theorems.Thm_R03ThreeVertexSeparatorCandidate_three_vertex_connected_external_boundary_card_ge_three
-- name    : R03ThreeVertexSeparatorCandidate.three_vertex_connected_external_boundary_card_ge_three
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:18:04.968586+00:00
-- url     : https://prove2.me/theorems/a14378a3-ae6d-458d-ab13-29889265fb34
-- title:
--   Three vertex connected external boundary card ge three
-- statement:
--   If both the set and the part remaining after deleting its external boundary are nonempty, three-vertex-connectivity forces that boundary to have at least three vertices.
--
--   $$|N(Q)\setminus Q|\ge 3.$ $
--
--   This isolates one reusable separator or external-boundary statement in a finite three-vertex-connected graph. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_cubic_p3_partition_external_boundary

namespace R03ThreeVertexSeparatorCandidate

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

open CubicP3Partition

theorem three_vertex_connected_external_boundary_card_ge_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (Q : Finset V)
    (hQ : Q.Nonempty)
    (hR : (Finset.univ \ (Q ∪ externalBoundary G Q)).Nonempty) :
    3 ≤ (externalBoundary G Q).card := by sorry

end R03ThreeVertexSeparatorCandidate
