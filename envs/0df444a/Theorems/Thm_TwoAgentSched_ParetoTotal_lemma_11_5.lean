-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoTotal_lemma_11_5
-- name    : TwoAgentSched.ParetoTotal.lemma_11_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:29:46.676983+00:00
-- url     : https://prove2.me/theorems/ba0e6781-8745-4980-b8b3-3c0379679696
-- title:
--   Lemma 11.5 — once a B-job overtakes an A-job, it stays ahead as the bound decreases
-- statement:
--   Consider $1\|\sum C^A_i : f^B_{\max}\le Q$ with positive processing times $p_j>0$ and nondecreasing cost functions $f^B_k$. Let $Q'<Q$, let $\sigma$ be an optimal schedule for the bound $Q$ and $\sigma'$ an optimal schedule for the bound $Q'$, and suppose that in both the $A$-jobs follow the SPT order (shortest first, equal lengths by index). If a $B$-job $k$ precedes an $A$-job $j$ in $\sigma$, then
--   $$k\ \text{precedes}\ j\ \text{also in}\ \sigma'.$$
--
--   In the paper's words: once a $B$-job overtakes an $A$-job as $Q$ decreases, no reverse overtake occurs when $Q$ decreases further. This is the monotonicity behind the bound on the number of nondominated pairs (Theorem 11.6).
--
--   **Formalization Note** As for Lemma 11.4, the order of identical $A$-jobs must be the same in both schedules: with two $A$-jobs of length $1$ and one $B$-job whose cost is $0$ when it completes by time $2$ and $10$ afterwards, the schedules $a_2\,k\,a_1$ and $a_1\,k\,a_2$ are both optimal for $Q=1$ and for $Q'=1/2$, and $k$ precedes $a_1$ in the first but not in the second. The SPT order with ties by index is therefore a hypothesis on both schedules.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 240, Lemma 11.5

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoTotal_Model

namespace TwoAgentSched.ParetoTotal

/-- Lemma 11.5 (Agnetis et al. 2004, §11.2, p. 240), with the A-jobs of both schedules in the
fixed SPT order. Let `σ` be an optimal schedule of `1‖ΣC^A_i : f^B_max ≤ Q` in which the B-job
`k` precedes the A-job `j`, and let `σ′` be an optimal schedule of `1‖ΣC^A_i : f^B_max ≤ Q′`
with `Q′ < Q`, the A-jobs of both following the SPT order with ties broken by index. Then `k`
precedes `j` also in `σ′`. Processing times are positive. -/
theorem lemma_11_5 {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q Q' : ℝ) (hQ : Q' < Q)
    (σ σ' : List (TwoAgentSched.MaxMax.Job nA nB)) (hσ : TwoAgentSched.TotalMax.IsOptimal p fB Q σ) (hσ' : TwoAgentSched.TotalMax.IsOptimal p fB Q' σ')
    (hspt : AFollowsSPT p σ) (hspt' : AFollowsSPT p σ') (k : Fin nB) (j : Fin nA)
    (hkj : BPrecedesA σ k j) :
    BPrecedesA σ' k j := by sorry

end TwoAgentSched.ParetoTotal
