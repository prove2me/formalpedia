-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoMax_theorem_11_3
-- name    : TwoAgentSched.ParetoMax.theorem_11_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:28.851539+00:00
-- url     : https://prove2.me/theorems/0a4b577c-5154-4535-b923-7078b2d3ddc1
-- title:
--   Theorem 11.3 (corrected) — at most $n_An_B+1$ nondominated pairs in $1\|f^A_{\max}\circ f^B_{\max}$
-- statement:
--   Two agents share one machine: agent A has $n_A\ge1$ jobs and agent B has $n_B\ge1$ jobs, with nonnegative processing times; every job has a nondecreasing (regular) cost function of its completion time, and each agent evaluates a schedule $\sigma$ by the largest cost among its own jobs, $f^A_{\max}(\sigma)$ and $f^B_{\max}(\sigma)$. A pair $(y^A,y^B)$ is a **nondominated pair** if $y^A=f^A_{\max}(\sigma)$ and $y^B=f^B_{\max}(\sigma)$ for some schedule $\sigma$ that no other schedule improves for one agent without worsening it for the other. Let $\mathcal N$ be the set of nondominated pairs. Then
--   $$|\mathcal N|\le n_A\,n_B+1 .$$
--
--   The paper prints the bound as "there are at most $n_An_B$ nondominated schedules", with one schedule associated with each nondominated pair. That bound is off by one: with $n_A=n_B=1$, $p\equiv1$ and $f^A(t)=f^B(t)=t$, the schedules AB and BA give the two nondominated pairs $(1,2)$ and $(2,1)$. The printed proof counts the order reversals between consecutive schedules (at most $n_An_B$) and omits the first schedule; the corrected bound adds it.
--
--   The result shows that the Pareto front of the two-agent maximum-cost problem has polynomially many points, so it can be enumerated by solving polynomially many constrained problems $1\|f^A_{\max}:f^B_{\max}\le Q$.
--
--   **Formalization Note** The count is over pairs (a set of points of $\mathbb R^2$), measured with `Set.encard`, so finiteness is part of the statement. Schedules with the same pair are counted once. Nonnegative processing times and regular costs are the paper's standing assumptions (§3).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 240, Theorem 11.3 (printed bound n_A n_B corrected to n_A n_B + 1); p. 239, §11 (one schedule per nondominated pair)

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoMax_Model

namespace TwoAgentSched.ParetoMax

/-- Theorem 11.3 (p. 240), corrected. In `1‖f^A_max ∘ f^B_max` there are at most `n_A n_B + 1`
nondominated pairs `(y^A, y^B)` (the paper associates one nondominated schedule with each pair
and prints the bound `n_A n_B`, which fails already for `n_A = n_B = 1`). Processing times are
nonnegative and all costs nondecreasing (regular). -/
theorem theorem_11_3 {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k)) :
    (ndPairs hA hB p fA fB).encard ≤ ((nA * nB + 1 : ℕ) : ℕ∞) := by sorry

end TwoAgentSched.ParetoMax
