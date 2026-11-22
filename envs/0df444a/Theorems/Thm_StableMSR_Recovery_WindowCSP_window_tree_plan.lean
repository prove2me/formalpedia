-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_window_tree_plan
-- name    : StableMSR.Recovery.WindowCSP.window_tree_plan
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:10:31.049488+00:00
-- url     : https://prove2.me/theorems/84c2497a-cae8-4bfb-98a5-503729da7afc
-- title:
--   Exact real-valued regional window tables with explicit width and join-volume bounds
-- statement:
--   Instantiate the pairwise exact-count recurrence on 4R window traces. At every feasible count the regional table has a minimizing entry and an actual compatible assignment attaining its true real-valued cost. At width w its per-bag choice bound is ((h+1)n^(2(h+1))+1)^(w+1), with at most 2n+1 plan nodes. These statements hold for arbitrary input windows and radii whenever the interaction graph has the supplied width.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.WindowCSP.window_tree_plan (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) w) :
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n),realizesWindows x W R h w p := by
  sorry
