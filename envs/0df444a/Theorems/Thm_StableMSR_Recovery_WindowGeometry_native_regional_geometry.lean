-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_native_regional_geometry
-- name    : StableMSR.Recovery.WindowGeometry.native_regional_geometry
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:30:39.902478+00:00
-- url     : https://prove2.me/theorems/b06c8425-acd2-4c40-b72d-4bbbae548353
-- title:
--   A fixed polynomial distance-RAM program constructs the canonical geometry for a regional window problem
-- statement:
--   From a region membership bitmap and two endpoint identifiers specifying its scale, one deterministic native command constructs the canonical greedy net, all least covering anchors, and both the window-incidence and interaction-graph matrices. Its runtime is polynomial in the allocated dimensions and independent of the stability parameter.
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

theorem StableMSR.Recovery.WindowGeometry.native_regional_geometry : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → 2+x.n+x.n*x.n≤ x.rows →
    Ready x s → ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧
    Ready (worldOf x.k x.rows x.dist t) t ∧ Atlas x (worldOf x.k x.rows x.dist t).mem := by sorry
