-- Prove2me | Theorems.Thm_StableMSR_Recovery_FewBallRows_append_few_large_recovery
-- name    : StableMSR.Recovery.FewBallRows.append_few_large_recovery
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T23:21:24.216435+00:00
-- url     : https://prove2.me/theorems/3959c638-09f7-4b76-921f-cc84e9ebdbd0
-- title:
--   Exact distance-RAM recovery for a bounded number of large clusters
-- statement:
--   A deterministic distance-RAM command extends any existing candidate table by exactly $n^{2(h+1)}$ rows. For each stable partition with at most $h$ large clusters, one appended row covers the full metric at its exact cost. All earlier good rows keep their scores, and a single polynomial bounds the overhead in the input dimensions and the number of added rows. The number of small clusters is unrestricted.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem StableMSR.Recovery.FewBallRows.append_few_large_recovery : ∃p : Polynomial ℕ,∀h : ℕ,∃cmd : Cmd,∀(x : World) (s : Store),
    1 ≤ x.k → x.k < x.n → h < x.k → IsMetricArray x.dist → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval (x.cap + rows x.n (h+1)) ∧
    let y := worldOf x.k (x.rows + rows x.n (h+1)) x.dist t
    Ready y t ∧ (endpoints x → endpoints y) ∧
    (∀r < x.rows,good x r → good y r ∧ score y r=score x r) ∧
    ∀(e : ℝ),0 < e → e < 1 → ∀O,Stable x.dist x.k (1+e) O →
      (largeClusters x.dist O e).card ≤ h →
      ∃u < rows x.n (h+1),good y (x.rows+u) ∧ score y (x.rows+u)=cost x.dist O := by
  sorry
