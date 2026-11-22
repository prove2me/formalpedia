-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
-- name    : StableMSR.Recovery.WindowCSP.pairwise_windows_glue
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:04:31.683666+00:00
-- url     : https://prove2.me/theorems/2c5edcfc-1807-4fbf-8b97-8e259e53da02
-- title:
--   Pairwise checks on the 8R graph glue overlapping windows into a feasible partition
-- statement:
--   Every core point is covered by its window partition. Two candidate blocks sharing a point can disagree only at anchors within 8R, where the pairwise constraint enforces equality. A surviving block is emitted exactly once, by the anchor of its least point. Counts and true sum-of-radii costs therefore add without duplication.
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

theorem StableMSR.Recovery.WindowCSP.pairwise_windows_glue (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (P : Pick x.n)
    (dm : IsMetricArray x.dist) (hr : 0≤R) (ok : valid x W R h P) :
    Feasible W (number x W R P) (WindowCSP.output x W R P) ∧
    cost x.dist (WindowCSP.output x W R P)=WindowCSP.price x W R P ∧
    WindowCSP.output x W R P=(greedyNet x.dist R W).biUnion (fun a=>accepted (anchor x.dist W R) a (P a)) := by
  sorry
