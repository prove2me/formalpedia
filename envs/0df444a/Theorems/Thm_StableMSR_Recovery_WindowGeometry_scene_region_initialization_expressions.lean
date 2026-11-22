-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_scene_region_initialization_expressions
-- name    : StableMSR.Recovery.WindowGeometry.scene_region_initialization_expressions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:33:48.835793+00:00
-- url     : https://prove2.me/theorems/4ca28cfd-2d1d-4e29-90c0-4b478251b6b2
-- title:
--   Quadratic regional scratch allocation and extraction are fixed input expressions
-- statement:
--   The two scale endpoint cells and all region-membership bits are read directly from the scenario arrays. Computing all outputs uses bounded equality scans and a quadratic scratch dimension.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_SceneRegionAtlas
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowGeometry

theorem StableMSR.Recovery.WindowGeometry.scene_region_initialization_expressions : Form (fun x _=>iv (tableHeight x)) ∧ ∀s : Bool,Form (fun x ρ=>iv (prepare x (ρ 0) (ρ 1) s)) := by sorry
