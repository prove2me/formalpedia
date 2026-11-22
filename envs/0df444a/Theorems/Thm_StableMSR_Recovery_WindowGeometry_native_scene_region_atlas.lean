-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_native_scene_region_atlas
-- name    : StableMSR.Recovery.WindowGeometry.native_scene_region_atlas
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:33:44.389799+00:00
-- url     : https://prove2.me/theorems/d20f0a04-d509-4a2b-a999-af9c322e364d
-- title:
--   Construct the full canonical regional window geometry directly from a raw scenario
-- statement:
--   One deterministic real-distance program starts at the original scene-label array with a specified scenario and regional representative in the two header cells. It returns the paper’s net, least anchors, closed-window membership and interaction adjacency in only n squared plus n plus two output rows. No precomputed region bitmap or supplied net is needed.
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

theorem StableMSR.Recovery.WindowGeometry.native_scene_region_atlas : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧
      let y:=worldOf x.k (tableHeight x) x.dist t
      Ready y t ∧ SceneAtlas x (x.mem 0).toNat (x.mem 1).toNat y.mem := by sorry
