-- Prove2me | Theorems.Thm_TwoAgentSched_TotalMax_lemma_5_6
-- name    : TwoAgentSched.TotalMax.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:35.694339+00:00
-- url     : https://prove2.me/theorems/322c0c66-ad5a-4c77-9e2b-aa9acfafa91a
-- title:
--   Lemma 5.6 — all optimal schedules have the same B-blocks in the same time intervals
-- statement:
--   Consider a feasible instance of $1\|\sum C^A_i : f^B_{\max}\le Q$ with positive processing times and nondecreasing $B$-cost functions. A **B-block** of a schedule is a maximal set of consecutive $B$-jobs in it. For any two optimal schedules $\sigma^*$ and $\sigma'$:
--
--   1. the partition of the $B$-jobs into B-blocks is the same: every $B$-job $J^B_k$ has the same B-block in $\sigma^*$ as in $\sigma'$;
--   2. the B-blocks are scheduled in the same time intervals: the B-block of each $J^B_k$ starts at the same time and ends at the same time in $\sigma^*$ as in $\sigma'$.
--
--   The lemma characterises optimal schedules: they differ only in the order of the jobs inside each B-block and in the order of identical $A$-jobs. This is what reduces nondominance to a single-agent problem inside each block.
--
--   **Formalization Note** The partition is compared through the block of each $B$-job, which determines it. The interval of a block is $[\min(C^B_{k'}-p^B_{k'}),\ \max C^B_{k'}]$ over the jobs $k'$ of the block. Positive processing times are assumed.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Lemma 5.6 (B-block defined just before it)

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_BBlock

namespace TwoAgentSched.TotalMax

/-- Lemma 5.6 (Agnetis et al. 2004, §5.2.1, p. 234). Given a feasible instance of
`1‖ΣC^A_i : f^B_max ≤ Q`, any two optimal schedules `σ*`, `σ′` have
(1) the same partition of the B-jobs into B-blocks: every B-job has the same B-block in both;
(2) their B-blocks scheduled in the same time intervals: every B-block starts and ends at the
same times in both. Processing times are positive. -/
theorem lemma_5_6 {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q) (σstar σ' : List (TwoAgentSched.MaxMax.Job nA nB))
    (hstar : IsOptimal p fB Q σstar) (h' : IsOptimal p fB Q σ') :
    (∀ k : Fin nB, bBlock σstar k = bBlock σ' k) ∧
      ∀ k : Fin nB, blockStart p σstar k = blockStart p σ' k ∧
        blockEnd p σstar k = blockEnd p σ' k := by sorry

end TwoAgentSched.TotalMax
