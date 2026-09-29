-- Prove2me | Theorems.Thm_R03ThreeVertexSeparatorCandidate_not_reachable_across_partition
-- name    : R03ThreeVertexSeparatorCandidate.not_reachable_across_partition
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:18:23.55985+00:00
-- url     : https://prove2.me/theorems/46172f08-1ca0-4d20-a377-a59dd5b9318e
-- title:
--   Not reachable across partition
-- statement:
--   A walk cannot move from one side of a partition to the other when no edge joins the two sides.
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

theorem not_reachable_across_partition
    {U : Type u} (H : SimpleGraph U)
    (A B : Set U)
    (hdisj : Disjoint A B)
    (hpart : ∀ x, x ∈ A ∨ x ∈ B)
    (hno : ∀ {x y}, x ∈ A → y ∈ B → ¬ H.Adj x y)
    {u v : U} (hu : u ∈ A) (hv : v ∈ B) :
    ¬ H.Reachable u v := by sorry

end R03ThreeVertexSeparatorCandidate
