-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_regional_geometry_expressions
-- name    : StableMSR.Recovery.WindowGeometry.regional_geometry_expressions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:30:32.701266+00:00
-- url     : https://prove2.me/theorems/908faf9a-1bc0-44d1-922a-c731a85b2c49
-- title:
--   The net scan, anchor selection, window matrix and graph matrix are fixed oracle expressions
-- statement:
--   Each pass uses integer membership scans and real distance comparisons at scales two, four and eight. Anchor ties use increasing point identifiers. All operations are uniform across regions and stability factors.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_RegionAtlas
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

theorem StableMSR.Recovery.WindowGeometry.regional_geometry_expressions : (∀s : Bool,Form (fun x ρ=>iv (reset x (ρ 0) (ρ 1) s))) ∧
    (∀s : Bool,Form (fun x ρ=>iv (sweep x (ρ 0) (ρ 1) s))) ∧
    (∀s : Bool,Form (fun x ρ=>iv (expose x (ρ 0) (ρ 1) s))) := by sorry
