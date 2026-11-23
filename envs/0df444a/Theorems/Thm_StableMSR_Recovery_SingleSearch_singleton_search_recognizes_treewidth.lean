-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_search_recognizes_treewidth
-- name    : StableMSR.Recovery.SingleSearch.singleton_search_recognizes_treewidth
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T23:59:37.564395+00:00
-- url     : https://prove2.me/theorems/ad7b12d1-2d05-4da3-95f7-c20d0413fa8a
-- title:
--   The single-vertex deletion recurrence recognizes treewidth exactly
-- statement:
--   Restriction to one new vertex per production is complete and sound. Recognition takes at most the number of vertices many recursion levels per component, including on disconnected and empty graphs.
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

theorem StableMSR.Recovery.SingleSearch.singleton_search_recognizes_treewidth {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    starts G w ↔ TreewidthLE G w := by sorry
