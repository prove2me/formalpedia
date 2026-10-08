-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoTotal_theorem_11_6
-- name    : TwoAgentSched.ParetoTotal.theorem_11_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:30:30.751076+00:00
-- url     : https://prove2.me/theorems/cf97c7e9-9cb5-41bc-9ce5-bfb37f30c116
-- title:
--   Theorem 11.6 (corrected) — at most n_A n_B + 1 nondominated pairs in 1‖ΣC^A_i ∘ f^B_max
-- statement:
--   Consider two agents on a single machine: agent $A$ owns $n_A$ jobs and minimizes its total completion time $\sum_h C^A_h$, agent $B$ owns $n_B\ge 1$ jobs, each with a nondecreasing cost function $f^B_k$ of its completion time, and minimizes $f^B_{\max}=\max_k f^B_k(C^B_k)$. Processing times are positive. Then the set $\mathcal P$ of nondominated pairs $\bigl(\sum C^A_h(\sigma),\,f^B_{\max}(\sigma)\bigr)$, over all nondominated schedules $\sigma$, is finite and
--   $$|\mathcal P|\ \le\ n_A\,n_B+1.$$
--
--   The bound says that the Pareto frontier of this bicriteria problem has polynomial size, so the scheme PP of §11, which solves the constrained problem $1\|\sum C^A_i : f^B_{\max}\le Q$ for decreasing $Q$, enumerates it with polynomially many calls.
--
--   **Formalization Note** The paper prints "There are at most $n_An_B$ nondominated schedules in $1\|\sum C^A_i\circ f^B_{\max}$". That bound is false by one: for $n_A=n_B=1$, $p\equiv 1$ and $f^B(t)=t$, the schedules $AB$ and $BA$ give the two nondominated pairs $(1,2)$ and $(2,1)$, while $n_An_B=1$. The proof counts at most one overtake per consecutive pair of schedules of PP and does not count the first schedule; the corrected bound is $n_An_B+1$. "Schedules" is read as pairs, one schedule per pair, as in §11. The cardinality is `Set.encard`, which is infinite on an infinite set, so the statement also asserts finiteness. The hypothesis $n_B\ge 1$ makes $f^B_{\max}$ defined.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 241, Theorem 11.6 (bound corrected from n_A n_B to n_A n_B + 1)

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoTotal_Pareto

namespace TwoAgentSched.ParetoTotal

/-- Theorem 11.6, corrected (Agnetis et al. 2004, §11.2, p. 241). In `1‖ΣC^A_i ∘ f^B_max`
with at least one B-job, positive processing times and nondecreasing cost functions `f^B_k`,
there are at most `n_A n_B + 1` nondominated pairs `(ΣC^A_i, f^B_max)`. (The printed bound
`n_A n_B` is off by one: `n_A = n_B = 1`, `p ≡ 1`, `f^B(t) = t` has the two nondominated pairs
`(1, 2)` and `(2, 1)`.) `Set.encard` is `⊤` on an infinite set, so the bound also asserts that
there are finitely many pairs. -/
theorem theorem_11_6 {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) :
    (ndPairs hB p fB).encard ≤ ((nA * nB + 1 : ℕ) : ℕ∞) := by sorry

end TwoAgentSched.ParetoTotal
