-- Prove2me | Theorems.Thm_StableMSR_Recovery_RegionalSeeds_bounded_overlap_regional_recovery
-- name    : StableMSR.Recovery.RegionalSeeds.bounded_overlap_regional_recovery
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T13:19:23.939806+00:00
-- url     : https://prove2.me/theorems/055657ec-ddf4-41e2-a9a1-df3b7064dff7
-- title:
--   Exact-count recovery on any aligned partition of bounded local overlap
-- statement:
--   Given any aligned regional partition in which each region meets at most h large optimal clusters, independent local guess menus recover the global optimum by taking the least additive cost at total count k. The optimum is realized by one combination, all exact-count combinations are feasible, and all ties at the optimal cost recover the same partition. There is no bound on the total number of large clusters, the number of regions, or the number of small clusters per region.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission. Lemmas 3.3 and 3.8 supply the geometric seeds for the local-overlap variant.

import Definitions.Def_StableMSR_RegionalSeeds
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.RegionalSeeds.bounded_overlap_regional_recovery (x : World) (h : ℕ) (hk : 1≤x.k) (hn : x.k<x.n)
    (dm : IsMetricArray x.dist) (e : ℝ) (he : 0<e) (hl : e<1)
    (O R : Partition x.n) (hs : Stable x.dist x.k (1+e) O)
    (parts : Feasible Finset.univ R.card R)
    (aligned : ∀W∈R,Aligned O W)
    (overlap : ∀W∈R,(meeting (largeClusters x.dist O e) W).card≤h) :
    (∀W∈R,(RegionalSeeds.traceMenu x h W).card≤(h+1)*rows x.n (h+1)) ∧
    (∃T : Cluster x.n→Partition x.n,(∀W∈R,T W∈RegionalSeeds.traceMenu x h W) ∧
      (∑W ∈ R,(T W).card)=x.k ∧ R.biUnion T=O ∧
      (∑W ∈ R,cost x.dist (T W))=cost x.dist O) ∧
    ∀T : Cluster x.n→Partition x.n,(∀W∈R,T W∈RegionalSeeds.traceMenu x h W) →
      (∑W ∈ R,(T W).card)=x.k →
      Feasible Finset.univ x.k (R.biUnion T) ∧
      cost x.dist (R.biUnion T)=(∑W ∈ R,cost x.dist (T W)) ∧
      cost x.dist O≤(∑W ∈ R,cost x.dist (T W)) ∧
      ((∑W ∈ R,cost x.dist (T W))=cost x.dist O → R.biUnion T=O) := by
  sorry
