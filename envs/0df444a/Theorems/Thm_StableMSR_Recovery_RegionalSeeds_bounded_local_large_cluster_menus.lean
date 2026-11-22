-- Prove2me | Theorems.Thm_StableMSR_Recovery_RegionalSeeds_bounded_local_large_cluster_menus
-- name    : StableMSR.Recovery.RegionalSeeds.bounded_local_large_cluster_menus
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T13:18:18.521374+00:00
-- url     : https://prove2.me/theorems/41ca2010-94ed-4426-99f9-7177242369ae
-- title:
--   Exact regional partition menus with only a local bound on large clusters
-- statement:
--   For any window W, enumerate at most (h+1)n^(2(h+1)) feasible partition candidates. The family contains all nonempty intersections of the stable optimum with W as one candidate whenever at most h globally large clusters meet W, irrespective of how many lie outside. For aligned W that candidate is the true restricted partition. One distance pair encodes the small-component threshold and one center/farthest-witness pair encodes each intersecting large ball.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_RegionalSeeds
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.RegionalSeeds.bounded_local_large_cluster_menus (x : World) (h : ℕ) (W : Cluster x.n) (hk : 1≤x.k) (hn : x.k<x.n)
    (dm : IsMetricArray x.dist) :
    (RegionalSeeds.traceMenu x h W).card≤(h+1)*rows x.n (h+1) ∧
    (∀P∈RegionalSeeds.traceMenu x h W,Feasible W P.card P) ∧
    ∀(e : ℝ),0<e → e<1 → ∀O,Stable x.dist x.k (1+e) O →
      (meeting (largeClusters x.dist O e) W).card≤h →
      RegionalSeeds.tracePartition O W∈RegionalSeeds.traceMenu x h W ∧
      (Aligned O W → restrictPartition O W∈RegionalSeeds.traceMenu x h W) := by
  sorry
