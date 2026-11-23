-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_labelled_component_language
-- name    : StableMSR.Recovery.SingleSearch.singleton_labelled_component_language
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T23:59:38.817801+00:00
-- url     : https://prove2.me/theorems/d28b77a5-cf77-4f8a-9e83-da95cb859762
-- title:
--   Exact assignment language of a singleton separator state
-- statement:
--   The independent recursive productions emit exactly the full interior assignments compatible with the prescribed boundary. All oriented edge tests, labels at individual vertices, and alternatives are preserved in both directions.
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

theorem StableMSR.Recovery.SingleSearch.singleton_labelled_component_language {V X : Type} [Fintype V] [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (w m : ℕ) (S C : Finset V)
    (hc : IsFlap G S C) (a : V→X) (O : Finset (V×X)) :
    run G D test w m S C a O ↔ one G w m S C ∧ ∃f : V→X,
      okay G D test (S∪C) f ∧ (∀v∈S,f v=a v) ∧ O=labels C f := by sorry
