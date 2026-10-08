-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoTotal_lemma_5_4
-- name    : TwoAgentSched.ParetoTotal.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:29:48.11516+00:00
-- url     : https://prove2.me/theorems/ce7812c4-96df-4f11-95f7-c7c2f4fb20fa
-- title:
--   Lemma 5.4 — if no B-job can end last, every optimal schedule ends with a longest A-job
-- statement:
--   Consider an instance of $1\|\sum C^A_i : f^B_{\max}\le Q$ with $n_A\ge 1$ $A$-jobs, positive processing times $p_j>0$ and nondecreasing cost functions $f^B_k$, and suppose the instance is feasible. Let $\tau=P_A+P_B$ be the total processing time of all jobs. If
--   $$f^B_k(\tau)>Q\qquad\text{for every }B\text{-job }J^B_k,$$
--   then in every optimal schedule the last job is a longest $A$-job, i.e. an $A$-job $J^A_h$ with $p^A_{h'}\le p^A_h$ for every $A$-job $J^A_{h'}$.
--
--   Applied to the jobs not yet scheduled, this is why the $A$-jobs of an optimal (and of a nondominated) schedule are in SPT order, the fact §11.2 opens with.
--
--   **Formalization Note** The statement is the same as the milestone `TwoAgentSched.TotalMax.lemma_5_4` of mission 3 of this series, restated here because draft items cannot import each other. The hypothesis $n_A\ge 1$ excludes the empty instance, whose empty schedule has no last job; positivity of the processing times is the paper's standing convention.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 234, Lemma 5.4

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoTotal_Model

namespace TwoAgentSched.ParetoTotal

/-- Lemma 5.4 (Agnetis et al. 2004, §5.2, p. 234). Consider a feasible instance of
`1‖ΣC^A_i : f^B_max ≤ Q` with at least one A-job, and let `τ = P_A + P_B`. If every B-job has
`f^B_k(τ) > Q`, then in every optimal schedule the last job is a longest A-job: an A-job `h`
with `p^A_{h'} ≤ p^A_h` for every A-job `h'`. -/
theorem lemma_5_4 {nA nB : ℕ} (hA : 0 < nA) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : TwoAgentSched.TotalMax.IsFeasibleInstance p fB Q)
    (hall : ∀ k : Fin nB,
      Q < fB k (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k))) :
    ∀ l : List (TwoAgentSched.MaxMax.Job nA nB), TwoAgentSched.TotalMax.IsOptimal p fB Q l →
      ∃ h : Fin nA, l.getLast? = some (Sum.inl h) ∧
        ∀ h' : Fin nA, p (Sum.inl h') ≤ p (Sum.inl h) := by sorry

end TwoAgentSched.ParetoTotal
