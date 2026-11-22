-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_aligned_scenario_has_exact_assignment
-- name    : StableMSR.Recovery.WindowCSP.aligned_scenario_has_exact_assignment
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:04:04.119767+00:00
-- url     : https://prove2.me/theorems/868ceca9-3564-410b-8383-2de91158da2e
-- title:
--   Aligned bounded-diameter scenarios have a bounded-treewidth assignment of exact global cost and count
-- statement:
--   Use the true 4R-window traces in every region of the supplied label partition. Alignment identifies the union of owned blocks with the actual optimal clusters inside the region. Summing their exact costs and counts recovers the full OPT and k. The interaction graphs have the mission’s treewidth bound by the stable bounded-diameter theorem.
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

theorem StableMSR.Recovery.WindowCSP.aligned_scenario_has_exact_assignment (x : World) (s : ℕ) (e : ℝ) (he : 0<e) (hl : e<1)
    (hk : 1≤x.k) (hn : x.k<x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0<scale x s) (eq : scale x s=largestRadius x.dist O)
    (al : ∀W∈regions x s,Aligned O W ∧ diameter x.dist W≤densityScale x.dist O e) :
    (∀W∈regions x s,RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x s) W) (widthBound e)) ∧
    ∃P : Cluster x.n→Pick x.n,(∀W∈regions x s,valid x W (scale x s) (budget e) (P W)) ∧
      (∑W ∈ regions x s,number x W (scale x s) (P W))=x.k ∧
      (∑W ∈ regions x s,WindowCSP.price x W (scale x s) (P W))=cost x.dist O := by
  sorry
