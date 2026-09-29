-- Prove2me | Theorems.Thm_R03ThreeVertexSeparatorCandidate_three_vertex_connected_separator_card_ge_three
-- name    : R03ThreeVertexSeparatorCandidate.three_vertex_connected_separator_card_ge_three
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:17:50.555777+00:00
-- url     : https://prove2.me/theorems/0e364b57-c711-4bc1-9ff0-3ed3c9517b98
-- title:
--   Three vertex connected separator card ge three
-- statement:
--   In a finite simple graph satisfying the project's three-vertex-connectivity predicate, every separator separating two nonempty sides has at least three vertices.
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

theorem three_vertex_connected_separator_card_ge_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (Q N R : Finset V)
    (hQN : Disjoint Q N)
    (hQR : Disjoint Q R)
    (hNR : Disjoint N R)
    (hcover : Q ∪ N ∪ R = Finset.univ)
    (hQ : Q.Nonempty)
    (hR : R.Nonempty)
    (hno : ∀ q ∈ Q, ∀ r ∈ R, ¬ G.Adj q r) :
    3 ≤ N.card := by sorry

end R03ThreeVertexSeparatorCandidate
