-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_regional_geometry_scan_correct
-- name    : StableMSR.Recovery.WindowGeometry.regional_geometry_scan_correct
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:30:51.351824+00:00
-- url     : https://prove2.me/theorems/e7c1733f-c1d0-4a33-aca4-3ed5b41f234b
-- title:
--   The synchronous real-distance scan recovers the canonical net and all geometric incidence entries
-- statement:
--   After t iterations the bitmap equals the paper’s greedy net on the first t input points. Scale and region data persist through every update. The final pass emits the least qualifying anchor with the prescribed fallback, exact closed four-radius windows and the eight-radius interaction graph.
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

theorem StableMSR.Recovery.WindowGeometry.regional_geometry_scan_correct (x : World) (hk : 0< x.k) (space : 2+x.n+x.n*x.n≤ x.rows)
    (h : ℕ→WindowProfiles.Mem) (m : WindowProfiles.Mem)
    (start : Writes x (WindowProfiles.replace x (h 0)) reset)
    (steps : ∀i< x.rows,Writes (WindowProfiles.replace x (h i)) (WindowProfiles.replace x (h (i+1))) sweep)
    (endpass : Writes (WindowProfiles.replace x (h x.rows)) (WindowProfiles.replace x m) expose) : Atlas x m := by sorry
