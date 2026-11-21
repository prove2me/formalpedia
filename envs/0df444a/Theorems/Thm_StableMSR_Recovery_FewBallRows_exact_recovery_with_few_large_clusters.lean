-- Prove2me | Theorems.Thm_StableMSR_Recovery_FewBallRows_exact_recovery_with_few_large_clusters
-- name    : StableMSR.Recovery.FewBallRows.exact_recovery_with_few_large_clusters
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T23:37:48.182866+00:00
-- url     : https://prove2.me/theorems/94f466c4-925a-428a-9a32-0a91aff085a5
-- title:
--   Exact stable MSR in time parameterized by the number of large clusters
-- statement:
--   For every bound $h$ there is one deterministic exact distance-oracle program with running time $n^{O(h+1)}$. It always halts with a valid exact-$k$ labeling. For every real $0<\varepsilon<1$ simultaneously, it recovers any $(1+\varepsilon)$-stable optimal partition with at most $h$ large clusters, where large means radius at least $\varepsilon R/4$. The number of small clusters and $k$ are unrestricted. The program depends on $h$ alone and receives no stability parameter.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem StableMSR.Recovery.FewBallRows.exact_recovery_with_few_large_clusters : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀h : ℕ,∃P : MinSumFPT.Program,DeterministicProgram P ∧
    ∀(n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n → IsMetricArray d →
      ∃t ≤ a*n^(b*(h+1)),
        let s := execute P n k d t
        s.halted=true ∧ s.work ≤ a*n^(b*(h+1)) ∧ ValidLabels n k s ∧
          ∀e : ℝ,0 < e → e < 1 → ∀O,Stable d k (1+e) O →
          (largeClusters d O e).card ≤ h → outputPartition n k s=O := by
  sorry
