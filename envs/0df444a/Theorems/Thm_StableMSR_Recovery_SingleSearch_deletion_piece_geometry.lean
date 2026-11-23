-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_deletion_piece_geometry
-- name    : StableMSR.Recovery.SingleSearch.deletion_piece_geometry
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:59:26.234794+00:00
-- url     : https://prove2.me/theorems/07d11d1c-8a8f-49e0-b318-c33cabcda1fc
-- title:
--   Deleting a progress bag partitions a tight component and localizes every child boundary
-- statement:
--   The child interiors are exactly the old interior outside the progress bag. They are mutually nonadjacent, and every child sees its true boundary in the parent bag, in the original graph.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleVertexSearch
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5

theorem StableMSR.Recovery.SingleSearch.deletion_piece_geometry {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S C B : Finset V)
    (hc : IsFlap G S C) (sb : S⊆B) (bc : B⊆S∪C) :
    let K:=children G B C
    K.biUnion id=C\B ∧ total B K=S∪C ∧
    (∀E∈K,IsFlap G (boundary G E) E ∧ Disjoint E B ∧ boundary G E⊆B ∧ rim G (S∪C) E=boundary G E) ∧
    ∀E∈K,∀F∈K,E≠F → Disjoint E F ∧ ∀u∈E,∀v∈F,¬G.Adj u v := by sorry
