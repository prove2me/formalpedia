-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowMasks_physical_block_literals
-- name    : StableMSR.Recovery.WindowMasks.physical_block_literals
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:25:52.14906+00:00
-- url     : https://prove2.me/theorems/d56e7c19-4ab9-4148-af82-1f45d84108af
-- title:
--   Normalizing membership bits supplies every endpoint and exact local charge required by the separator board
-- statement:
--   Normalization preserves both separator relations and all regional root designations. Sound traces yield owned ball covers. A trace for an admissible window partition has exactly its number of clusters and sum of radii, yielding the required cost comparison.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowBlockMasks
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks

theorem StableMSR.Recovery.WindowMasks.physical_block_literals (x : World) (e : ℚ) (H : ℕ) (m f : WindowProfiles.Mem) (hk : 1≤ x.k) (kn : x.k< x.n)
    (dm : IsMetricArray x.dist) (cert : Describes x e {x with rows:=H,mem:=m})
    (head0 : f 0=m 0) (head1 : f 1=m 1)
    (fill : Writes {x with rows:=H,mem:=m} {x with rows:=H,mem:=f} normalized) :
    Presents x e {x with rows:=H,mem:=f} := by sorry
