-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_fast_forward_selection_correct
-- name    : ScenarioReduction.ForwardSelection.fast_forward_selection_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:01:43.937519+00:00
-- url     : https://prove2.me/theorems/39e2e372-736e-4763-a554-35d6446db87f
-- title:
--   Theorem 2.5 — fast forward selection solves the forward selection principle, and $z^{[i]}_{u_i}=D_{J^{[i]}}$
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be scenarios in a finite-dimensional normed space with probabilities $p_i>0$, $\sum_ip_i=1$, and let $c$ be the cost (3) built from a growth function $h$ and a point $\omega_0$. Let $1\le n\le N$ and let $u_1,\dots,u_n$ be determined by Algorithm 2.4 (fast forward selection):
--   $$
--   c^{[1]}_{ku}=c(\omega_k,\omega_u),\qquad c^{[i]}_{ku}=\min\bigl\{c^{[i-1]}_{ku},c^{[i-1]}_{ku_{i-1}}\bigr\},\qquad z^{[i]}_u=\sum_{k\in J^{[i-1]}\setminus\{u\}}p_kc^{[i]}_{ku},
--   $$
--   $$
--   u_i\in\arg\min_{u\in J^{[i-1]}}z^{[i]}_u,\qquad J^{[0]}=\{1,\dots,N\},\quad J^{[i]}=J^{[i-1]}\setminus\{u_i\},
--   $$
--   with arbitrary tie-breaking in each arg min. Then $\{u_1,\dots,u_n\}$ is a solution of the forward selection principle, i.e. for each $i=1,\dots,n$
--   $$
--   u_i\in\arg\min_{u\in J^{[i-1]}}\ \sum_{k\in J^{[i-1]}\setminus\{u\}}p_k\min_{j\notin J^{[i-1]}\setminus\{u\}}c(\omega_k,\omega_j),\tag{16}
--   $$
--   and furthermore
--   $$
--   z^{[i]}_{u_i}=D_{J^{[i]}}\qquad(i=1,\dots,n),
--   $$
--   where $D_J=\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j)$ is the reduction cost (8).
--
--   The theorem shows that the cheap pairwise update of Algorithm 2.4 computes exactly the greedy forward selection of kept scenarios, and that its running objective value is the optimal distance (by Theorem 2.1) between the original measure and the measure reduced to the scenarios kept so far.
--
--   **Formalization Note** A run is any sequence satisfying the arg-min conditions, so the statement covers every tie-breaking rule. The paper's standing assumption $n<N$ is relaxed to $n\le N$; for $n=N$ the statement remains true ($D_\emptyset=0=z^{[N]}_{u_N}$), and Propositions 2.3 and 2.6 of the paper also use $n\in\{1,\dots,N\}$. The proof in the paper says "for $i=2,\dots,N$"; the theorem's range $i=2,\dots,n$ is used.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 194, Theorem 2.5; Algorithm 2.4, pp. 193–194; eq. (16), p. 193

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun

namespace ScenarioReduction.ForwardSelection

/-- Theorem 2.5, Heitsch–Römisch 2003, p. 194. For every run `u₁, …, uₙ` of Algorithm 2.4 (fast
forward selection), with any tie-breaking in its arg min, each `uᵢ` satisfies the forward selection
principle (16), and `z^{[i]}_{uᵢ} = D_{J^{[i]}}` for each `i = 1, …, n`. -/
theorem fast_forward_selection_correct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) (u : ℕ → Fin N)
    (hrun : IsFastForwardRun (scenCost h ω₀ ω) p n u) :
    IsForwardSelection (scenCost h ω₀ ω) p n u ∧
    ∀ i (hi : i ∈ Finset.Icc 1 n),
      zStep (scenCost h ω₀ ω) p u i (u i) =
        reductionCost (scenCost h ω₀ ω) p (Jstep u i)
          (Jstep_compl_nonempty u (Finset.mem_Icc.1 hi).1) := by sorry

end ScenarioReduction.ForwardSelection
