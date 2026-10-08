-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoTotal_lemma_11_4
-- name    : TwoAgentSched.ParetoTotal.lemma_11_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:29:45.114634+00:00
-- url     : https://prove2.me/theorems/503dc26f-ee58-4343-a1cf-6ed64d682069
-- title:
--   Lemma 11.4 — tightening the bound on B never lets an A-job complete earlier
-- statement:
--   Consider $1\|\sum C^A_i : f^B_{\max}\le Q$ with positive processing times $p_j>0$ and nondecreasing cost functions $f^B_k$. Let $Q'<Q$, let $\sigma$ be an optimal schedule for the bound $Q$ and $\sigma'$ an optimal schedule for the bound $Q'$, and suppose that in both the $A$-jobs follow the SPT order (shortest first, equal lengths by index). Then for every $A$-job $j$,
--   $$C_j(\sigma')\ \ge\ C_j(\sigma).$$
--
--   As the constraint on agent $B$ becomes tighter, the completion time of no $A$-job can decrease. Lemma 11.5 is a direct consequence.
--
--   **Formalization Note** The paper's statement fixes no order on identical $A$-jobs, and then it is false: with two $A$-jobs of length $1$ and no constrained $B$-job, $a_1a_2$ and $a_2a_1$ are both optimal for every bound, and $a_2$ completes at $1$ in the second and at $2$ in the first. The paper's proof uses that "the $A$-jobs preceding $j$ in $\sigma'$ are the same as in $\sigma$", which holds when both schedules order the $A$-jobs the same way; hence the SPT-order hypotheses. Every optimal schedule can be brought to this order by swapping identical $A$-jobs, which changes neither objective.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 240, Lemma 11.4

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoTotal_Model

namespace TwoAgentSched.ParetoTotal

/-- Lemma 11.4 (Agnetis et al. 2004, §11.2, p. 240), with the A-jobs of both schedules in the
fixed SPT order. Let `σ` be an optimal schedule of `1‖ΣC^A_i : f^B_max ≤ Q` and `σ′` an optimal
schedule of `1‖ΣC^A_i : f^B_max ≤ Q′` with `Q′ < Q`, the A-jobs of both following the SPT order
with ties broken by index. Then no A-job completes earlier in `σ′`: `C_j(σ′) ≥ C_j(σ)` for every
A-job `j`. Processing times are positive. -/
theorem lemma_11_4 {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q Q' : ℝ) (hQ : Q' < Q)
    (σ σ' : List (TwoAgentSched.MaxMax.Job nA nB)) (hσ : TwoAgentSched.TotalMax.IsOptimal p fB Q σ) (hσ' : TwoAgentSched.TotalMax.IsOptimal p fB Q' σ')
    (hspt : AFollowsSPT p σ) (hspt' : AFollowsSPT p σ') (j : Fin nA) :
    MooreLateJobs.Shared.completionTime p σ (Sum.inl j) ≤
      MooreLateJobs.Shared.completionTime p σ' (Sum.inl j) := by sorry

end TwoAgentSched.ParetoTotal
