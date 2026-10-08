-- Prove2me | Theorems.Thm_TwoAgentSched_TotalMax_lemma_5_4
-- name    : TwoAgentSched.TotalMax.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:04.003728+00:00
-- url     : https://prove2.me/theorems/778cd314-418b-4076-bdc6-174c8db423e3
-- title:
--   Lemma 5.4 — if no B-job can end last, every optimal schedule ends with a longest A-job
-- statement:
--   Consider the problem $1\|\sum C^A_i : f^B_{\max}\le Q$ (positive processing times, nondecreasing $f^B_k$, feasibility $f^B_k(C^B_k)\le Q$ for all $k$), with at least one $A$-job. Assume the instance is feasible, and let $\tau=P_A+P_B$ be the total processing time. If
--   $$f^B_k(\tau)>Q\quad\text{for every } B\text{-job } J^B_k,$$
--   then in every optimal schedule the last job is a longest $A$-job: an $A$-job $J^A_h$ with $p^A_{h'}\le p^A_h$ for all $h'$.
--
--   This lemma justifies the second branch of the algorithm of Figure 1. When several $A$-jobs have the maximum length, the lemma does not say which of them is last.
--
--   **Formalization Note** The hypothesis $n_A\ge 1$ excludes the instance with no jobs at all, whose empty schedule is feasible and has no last job; the paper's "a longest $A$-job" presupposes $A$-jobs.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Lemma 5.4

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.TotalMax

/-- Lemma 5.4 (Agnetis et al. 2004, §5.2, p. 234). Consider a feasible instance of
`1‖ΣC^A_i : f^B_max ≤ Q` with at least one A-job, and let `τ = P_A + P_B`. If every B-job has
`f^B_k(τ) > Q`, then in every optimal schedule the last job is a longest A-job: an A-job `h`
with `p^A_{h'} ≤ p^A_h` for every A-job `h'`. -/
theorem lemma_5_4 {nA nB : ℕ} (hA : 0 < nA) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q)
    (hall : ∀ k : Fin nB,
      Q < fB k (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k))) :
    ∀ l : List (TwoAgentSched.MaxMax.Job nA nB), IsOptimal p fB Q l →
      ∃ h : Fin nA, l.getLast? = some (Sum.inl h) ∧
        ∀ h' : Fin nA, p (Sum.inl h') ≤ p (Sum.inl h) := by sorry

end TwoAgentSched.TotalMax
