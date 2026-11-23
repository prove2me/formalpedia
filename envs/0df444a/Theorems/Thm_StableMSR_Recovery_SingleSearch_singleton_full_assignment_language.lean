-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_full_assignment_language
-- name    : StableMSR.Recovery.SingleSearch.singleton_full_assignment_language
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:59:49.241456+00:00
-- url     : https://prove2.me/theorems/2859752d-5778-4127-a30b-2385005d72f4
-- title:
--   The root grammar generates exactly the feasible full assignments at width w
-- statement:
--   The root output records every vertex label of one legal solution, and generates each legal solution on a graph of width at most w. Disconnected components, empty domains and the empty graph are included.
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

theorem StableMSR.Recovery.SingleSearch.singleton_full_assignment_language {V X : Type} [Fintype V] [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (w : ℕ) (a : V→X) (O : Finset (V×X)) :
    root G D test w a O ↔ TreewidthLE G w ∧ ∃f : V→X,okay G D test Finset.univ f ∧ O=labels Finset.univ f := by sorry
