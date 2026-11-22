-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_port_packing_preserves_derivations
-- name    : StableMSR.Recovery.WindowPorts.port_packing_preserves_derivations
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:21:29.841613+00:00
-- url     : https://prove2.me/theorems/a5d16413-c646-4172-b79b-e48b68a17d63
-- title:
--   The physical five-band expansion preserves all port witnesses and all regional roots
-- statement:
--   The physical count and production fields recover the abstract lowering. Designated regional roots preserve every endpoint witness in both directions, including the empty word for unused regional indices.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPortPacking
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts

theorem StableMSR.Recovery.WindowPorts.port_packing_preserves_derivations (x : World) (e : ℚ) (H : ℕ) (m f : WindowProfiles.Mem) (hk : 1≤ x.k) (kn : x.k< x.n)
    (cert : Presents x e {x with rows:=H,mem:=m})
    (fill : Writes {x with rows:=H,mem:=m} {x with rows:=H,mem:=f} WindowPorts.packed) :
    Encodes x e {x with rows:=H,mem:=f} := by sorry
