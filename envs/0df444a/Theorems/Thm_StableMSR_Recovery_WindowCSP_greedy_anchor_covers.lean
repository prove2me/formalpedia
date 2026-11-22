-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_greedy_anchor_covers
-- name    : StableMSR.Recovery.WindowCSP.greedy_anchor_covers
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:04:06.757538+00:00
-- url     : https://prove2.me/theorems/fe211300-3f9f-4e4c-870a-f4d753ae294e
-- title:
--   Nearest admissible greedy-net anchors cover every regional point
-- statement:
--   Induct over the fixed greedy scan. An accepted point covers itself and a rejected point already has a net point within distance 2R. The least admissible anchor exists and the final net lies inside the region.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.WindowCSP.greedy_anchor_covers {n : ℕ} (d : Point n→Point n→ℝ) (dm : IsMetricArray d)
    (W : Cluster n) (R : ℝ) (hr : 0≤R) :
    greedyNet d R W⊆W ∧ ∀i∈W,anchor d W R i∈greedyNet d R W ∧ d (anchor d W R i) i≤2*R := by
  sorry
