-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowMasks_canonical_block_endpoints
-- name    : StableMSR.Recovery.WindowMasks.canonical_block_endpoints
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:25:59.00384+00:00
-- url     : https://prove2.me/theorems/e4999b95-4292-4f18-ba3d-9f8ee02ae8b7
-- title:
--   Point membership alone determines a native word attaining the exact discrete block radius
-- statement:
--   Among all center and farthest-point pairs in a marked block, bounded scans select a pair attaining its discrete radius. Every tie is settled by the least possible center and then witness. An empty block contributes the empty word with cost zero.
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

theorem StableMSR.Recovery.WindowMasks.canonical_block_endpoints (x : World) (q : ℕ) (hk : 1≤ x.k) (hn : 0< x.n) :
    let C:=block x q;let c:=chargeCount x q;let w:=trimWord c (oneWord x q)
    c=(emit C).length ∧ Owned x C c w ∧ weight x c w=payment x.dist (emit C) ∧
    (∀j s,0≤ oneWord x q j s ∧ oneWord x q j s<(x.n:ℤ)) := by sorry
