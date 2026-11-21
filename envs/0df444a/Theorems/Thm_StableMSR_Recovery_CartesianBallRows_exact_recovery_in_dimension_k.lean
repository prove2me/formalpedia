-- Prove2me | Theorems.Thm_StableMSR_Recovery_CartesianBallRows_exact_recovery_in_dimension_k
-- name    : StableMSR.Recovery.CartesianBallRows.exact_recovery_in_dimension_k
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:33:16.50622+00:00
-- url     : https://prove2.me/theorems/954a71df-fbb5-4aa3-a330-bd9f0fdf491f
-- title:
--   Exact sum-of-radii optimization in n to the O(k) charged time
-- statement:
--   One finite deterministic distance-oracle program outputs a globally optimal exact-k partition on every finite metric input without any stability condition. It enumerates center and boundary-point pairs and minimizes over covering rows in charged n^{O(k)} time.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows

theorem StableMSR.Recovery.CartesianBallRows.exact_recovery_in_dimension_k : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∃P : MinSumFPT.Program,DeterministicProgram P ∧
    ∀(n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n → IsMetricArray d →
      ∃t ≤ a*n^(b*(k+1)),
        let s := execute P n k d t
        s.halted=true ∧ s.work ≤ a*n^(b*(k+1)) ∧ ValidLabels n k s ∧
          Optimal d Finset.univ k (outputPartition n k s) := by
  sorry
