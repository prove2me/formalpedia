-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_stable_region_exact_table
-- name    : StableMSR.Recovery.WindowCSP.stable_region_exact_table
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:09:41.990841+00:00
-- url     : https://prove2.me/theorems/4eab0af6-d282-4ecb-a315-1afd0114820a
-- title:
--   Exact regional recovery by a bounded-width real-cost table within the mission exponent
-- statement:
--   On any nonempty aligned region of diameter at most the density scale, the binary finite recurrence reconstructs the restricted optimum at its true count and cost. The proof bounds all raw join candidates by n raised to 70 times the mission parameter envelope. It allows arbitrarily many large clusters in the region. This supplies the finite-state local optimization argument independently of the remaining machine compilation.
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

theorem StableMSR.Recovery.WindowCSP.stable_region_exact_table (x : World) (W : Cluster x.n) (e : ℝ) (he : 0< e) (hl : e<1)
    (hk : 1≤ x.k) (hn : x.k< x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0< largestRadius x.dist O)
    (ne : W.Nonempty) (al : Aligned O W) (small : diameter x.dist W≤ densityScale x.dist O e) :
    let R:=largestRadius x.dist O
    let J:=restrictPartition O W
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n),
      realizesWindows x W R (budget e) (widthBound e) p ∧
      p.rawCandidateVolume x.k≤ x.n^(70*parameterEnvelope e) ∧
      ∃u∈TreeDP.solve x.k p,∃Q : Pick x.n,valid x W R (budget e) Q ∧
        u.2.1=J.card ∧ number x W R Q=J.card ∧ WindowCSP.output x W R Q=J ∧
        WindowCSP.price x W R Q=cost x.dist J ∧ u.2.2=cost x.dist J := by
  sorry
