-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_least_label_region_test
-- name    : StableMSR.Recovery.WindowGeometry.least_label_region_test
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:33:33.235592+00:00
-- url     : https://prove2.me/theorems/ccd3185a-3988-489c-a99e-c0f37fa09169
-- title:
--   A single bounded comparison of earlier labels recognizes each canonical scenario region
-- statement:
--   A point belongs to the region indexed i precisely when i is in range, has the same scenario label, and no smaller point has that label. The criterion handles repeated labels and empty slots.
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

theorem StableMSR.Recovery.WindowGeometry.least_label_region_test (x : World) (u i : ℕ) (p : Point x.n) : canonical x u i p.val ↔ p∈piece x u i := by sorry
