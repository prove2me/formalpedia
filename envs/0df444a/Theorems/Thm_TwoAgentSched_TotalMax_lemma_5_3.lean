-- Prove2me | Theorems.Thm_TwoAgentSched_TotalMax_lemma_5_3
-- name    : TwoAgentSched.TotalMax.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:55.252977+00:00
-- url     : https://prove2.me/theorems/bb9fef7b-48a6-48c3-8187-e0df622b14b5
-- title:
--   Lemma 5.3 — an eligible B-job can be placed last, and no optimal schedule ends with an A-job
-- statement:
--   Consider the problem $1\|\sum C^A_i : f^B_{\max}\le Q$ on one machine: agent $A$ owns jobs $J^A_1,\dots,J^A_{n_A}$, agent $B$ owns $J^B_1,\dots,J^B_{n_B}$, all processing times are positive, each $f^B_k$ is nondecreasing, and a schedule is feasible if $f^B_k(C^B_k)\le Q$ for all $k$. Assume the instance is feasible, and let
--   $$\tau=P_A+P_B=\sum_{h=1}^{n_A}p^A_h+\sum_{k=1}^{n_B}p^B_k$$
--   be the total processing time. If some $B$-job $J^B_{\bar k}$ satisfies $f^B_{\bar k}(\tau)\le Q$, then
--
--   1. there is an optimal schedule in which $J^B_{\bar k}$ is scheduled last, and
--   2. there is no optimal schedule in which an $A$-job is scheduled last.
--
--   This lemma justifies the first branch of the algorithm of Figure 1: a $B$-job that can afford to finish at the very end may be put there.
--
--   **Formalization Note** "Scheduled last" is the last entry of the sequence (`List.getLast?`). Positive processing times are assumed; without them part 2 fails, since a $B$-job of length zero can sit anywhere.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Lemma 5.3

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.TotalMax

/-- Lemma 5.3 (Agnetis et al. 2004, §5.2, p. 234). Consider a feasible instance of
`1‖ΣC^A_i : f^B_max ≤ Q` and let `τ = P_A + P_B`. If some B-job `J^B_{k̄}` has
`f^B_{k̄}(τ) ≤ Q`, then (1) some optimal schedule has `J^B_{k̄}` last, and (2) no optimal
schedule has an A-job last. Processing times are positive (needed for (2)). -/
theorem lemma_5_3 {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q) (kbar : Fin nB)
    (hkbar : fB kbar (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k)) ≤ Q) :
    (∃ l : List (TwoAgentSched.MaxMax.Job nA nB), IsOptimal p fB Q l ∧ l.getLast? = some (Sum.inr kbar)) ∧
      ∀ l : List (TwoAgentSched.MaxMax.Job nA nB), IsOptimal p fB Q l →
        ∀ h : Fin nA, l.getLast? ≠ some (Sum.inl h) := by sorry

end TwoAgentSched.TotalMax
