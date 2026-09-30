-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_backward_lower_bound
-- name    : ScenarioReduction.ForwardSelection.backward_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:59:11.853402+00:00
-- url     : https://prove2.me/theorems/0fceaecb-33e8-4430-b9c4-37a9ac8e8955
-- title:
--   Eq. (12) — the greedy single-deletion costs give a lower bound for problem (8)
-- statement:
--   Let $N\ge 2$, let $\omega_1,\dots,\omega_N$ be scenarios with probabilities $p_i>0$, $\sum_ip_i=1$, let $c$ be the cost (3), and let $n\in\mathbb N$ with $1\le n<N$. Let $l_1,\dots,l_{N-n}$ be selected by rule (11),
--   $$
--   l_i\in\arg\min_{l\in\{1,\dots,N\}\setminus\{l_1,\dots,l_{i-1}\}}p_l\min_{j\neq l}c(\omega_l,\omega_j),\qquad i=1,\dots,N-n .
--   $$
--   Then for every $J\subset\{1,\dots,N\}$ with $\#J=N-n$,
--   $$
--   lb:=\sum_{i=1}^{N-n}p_{l_i}\min_{j\neq l_i}c(\omega_{l_i},\omega_j)\;\le\;D_J ,
--   $$
--   so $lb$ is a lower bound of the optimal value of (8).
--
--   The bound is computable by sorting the single-deletion costs and certifies the quality of any heuristic solution of the NP-hard problem (8).
--
--   **Formalization Note** The paper states the bound as "can be shown" with a reference to earlier work; the statement is taken as printed. $N\ge 2$ is needed for $\min_{j\ne l}$ to be defined and follows from $1\le n<N$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 191, eqs. (11)–(12)

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsBackwardGreedy

namespace ScenarioReduction.ForwardSelection

/-- Eq. (12), Heitsch–Römisch 2003, p. 191. If `l₁, …, l_{N-n}` are selected by rule (11), then
`lb = ∑_{i=1}^{N-n} p_{lᵢ} min_{j ≠ lᵢ} c(ω_{lᵢ}, ωⱼ)` is at most `D_J` for every `J` with
`#J = N − n`, i.e. a lower bound of the optimal value of (8). -/
theorem backward_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hN : 1 < N) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n < N) (l : ℕ → Fin N)
    (hl : IsBackwardGreedy (scenCost h ω₀ ω) p hN (N - n) l)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (hcard : J.card = N - n) :
    ∑ i ∈ Finset.Icc 1 (N - n), singleCost (scenCost h ω₀ ω) p hN (l i) ≤
      reductionCost (scenCost h ω₀ ω) p J hJ := by sorry

end ScenarioReduction.ForwardSelection
