-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowGeometry_canonical_net_prefix
-- name    : StableMSR.Recovery.WindowGeometry.canonical_net_prefix
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:30:25.190505+00:00
-- url     : https://prove2.me/theorems/5094b646-aaa9-418b-b852-5c31d1e8813b
-- title:
--   The fixed-order net admits an exact one-point update on each input prefix
-- statement:
--   Extending a set of points by the next input index changes its sorted greedy net exactly when that index belongs to the region and is strictly farther than twice the scale from every currently selected point.
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

theorem StableMSR.Recovery.WindowGeometry.canonical_net_prefix {n : ℕ} (d : Point n→Point n→ℝ) (R : ℝ) (W : Cluster n) (p : Point n) :
    let U:=W.filter (fun i=>i.val< p.val);let N:=Supplement.greedyNet d R U
    Supplement.greedyNet d R (W.filter (fun i=>i.val< p.val+1))=
      if p∈W ∧ ∀s∈N,2*R< d p s then insert p N else N := by sorry
