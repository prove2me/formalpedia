-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_menu_tuple_envelope
-- name    : StableMSR.Recovery.SingleSearch.singleton_menu_tuple_envelope
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:11:16.585726+00:00
-- url     : https://prove2.me/theorems/5f993c8d-50e9-4810-8e48-58569bfe61c7
-- title:
--   The singleton candidate tuple fits the half exponent bound
-- statement:
--   Only one padded vertex tuple and one joint menu tuple are required. With three auxiliary point identifiers its entire rectangular candidate volume is bounded by the twenty-five-fold stability exponent. This is a per-region index count before filtering.
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

theorem StableMSR.Recovery.SingleSearch.singleton_menu_tuple_envelope (x : OracleQueries.World) (e : ℝ) (ep : 0< e) (el : e<1) (hn : 2≤ x.n) :
    x.n^3*(x.n+1)^(widthBound e+1)*WindowCSP.bagBound x (WindowCSP.budget e) (widthBound e)≤ x.n^(25*parameterEnvelope e) := by sorry
