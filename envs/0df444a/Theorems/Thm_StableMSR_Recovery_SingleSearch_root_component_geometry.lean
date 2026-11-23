-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_root_component_geometry
-- name    : StableMSR.Recovery.SingleSearch.root_component_geometry
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:59:29.819393+00:00
-- url     : https://prove2.me/theorems/73a97910-5727-40e5-8a79-2202e9d14272
-- title:
--   Root components partition the whole graph and have empty exterior boundary
-- statement:
--   At empty boundary all graph vertices lie in exactly one root component. No edge joins distinct root components and each component has empty neighborhood outside itself.
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

theorem StableMSR.Recovery.SingleSearch.root_component_geometry {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    let K:=PartialDecompositions.components G ∅
    K.biUnion id=Finset.univ ∧ (∀C∈K,boundary G C=∅) ∧
    ∀C∈K,∀E∈K,C≠E → Disjoint C E ∧ ∀u∈C,∀v∈E,¬G.Adj u v := by sorry
