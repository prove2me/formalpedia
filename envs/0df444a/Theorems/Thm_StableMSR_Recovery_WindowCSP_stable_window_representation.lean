-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_stable_window_representation
-- name    : StableMSR.Recovery.WindowCSP.stable_window_representation
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:04:03.567589+00:00
-- url     : https://prove2.me/theorems/4cf8ed47-a3c4-4fb8-8800-916534017082
-- title:
--   Stable regional traces are represented by pairwise choices of n to the O(1/epsilon) size
-- statement:
--   Apply the global large-cluster density bound at radius 4R, giving at most 24/epsilon intersecting large optimal blocks in every window. The bounded-overlap enumeration therefore lists the true trace at each anchor. A block meeting an anchor’s 2R core has diameter at most 2R and is fully visible inside its 4R window after intersection with W. Adjacent true choices agree, and the glued partition is exactly the global optimum restricted by intersection with W. The region may meet arbitrarily many large clusters.
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

theorem StableMSR.Recovery.WindowCSP.stable_window_representation (x : World) (W : Cluster x.n) (e : ℝ) (he : 0<e) (hl : e<1)
    (hk : 1≤x.k) (hn : x.k<x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0<largestRadius x.dist O) :
    let R:=largestRadius x.dist O
    let P : Pick x.n :=fun a=>tracePartition O (window x.dist W R a)
    (∀a : Point x.n,(meeting (largeClusters x.dist O e) (window x.dist W R a)).card≤budget e ∧
      (traceMenu x (budget e) (window x.dist W R a)).card≤(budget e+1)*CartesianBallRows.rows x.n (budget e+1)) ∧
    valid x W R (budget e) P ∧ WindowCSP.output x W R P=tracePartition O W := by
  sorry
