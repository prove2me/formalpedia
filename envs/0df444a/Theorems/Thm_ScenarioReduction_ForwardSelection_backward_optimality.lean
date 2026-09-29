-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_backward_optimality
-- name    : ScenarioReduction.ForwardSelection.backward_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:59:50.572227+00:00
-- url     : https://prove2.me/theorems/0e18eb1b-ff88-4a32-926b-89da1537ec61
-- title:
--   Sufficient optimality condition for the greedy set $\{l_1,\dots,l_{N-n}\}$ of rule (11)
-- statement:
--   Let $N\ge 2$, let $\omega_1,\dots,\omega_N$ be scenarios with probabilities $p_i>0$, $\sum_ip_i=1$, let $c$ be the cost (3), let $1\le n<N$, and let $l_1,\dots,l_{N-n}$ be selected by rule (11). Suppose that for every $i=1,\dots,N-n$ the set
--   $$
--   \arg\min_{j\neq l_i}c(\omega_{l_i},\omega_j)\setminus\{l_1,\dots,l_{i-1},l_{i+1},\dots,l_{N-n}\}
--   $$
--   is nonempty. Then $L=\{l_1,\dots,l_{N-n}\}$ is a solution of (8): it has $N-n$ elements and
--   $$
--   D_L=\min\bigl\{D_J:J\subset\{1,\dots,N\},\ \#J=N-n\bigr\}.
--   $$
--
--   When the condition holds, the greedy backward choice solves the set-covering problem (8) exactly; this is the motivation the paper gives for its backward reduction algorithms.
--
--   **Formalization Note** The conclusion bundles the nonemptiness of the complement of $L$ (needed for $D_L$ to be defined) with the explicit cardinality $\#L=N-n$ (so $L$ is feasible for (8)) and the statement that $D_L$ is the least element of $\{D_J:\#J=N-n\}$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 191, paragraph after eq. (12)

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsBackwardGreedy

namespace ScenarioReduction.ForwardSelection

/-- Sufficient optimality condition, Heitsch–Römisch 2003, p. 191. If `l₁, …, l_{N-n}` are selected
by rule (11) and, for every `i`, some minimizer of `c(ω_{lᵢ}, ωⱼ)` over `j ≠ lᵢ` lies outside
`{l₁, …, l_{i-1}, l_{i+1}, …, l_{N-n}}`, then `J = {l₁, …, l_{N-n}}` solves problem (8): it has
`N − n` elements and `D_J` is the minimum of `D_{J'}` over all `J'` with `#J' = N − n`. -/
theorem backward_optimality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hN : 1 < N) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n < N) (l : ℕ → Fin N)
    (hl : IsBackwardGreedy (scenCost h ω₀ ω) p hN (N - n) l)
    (hcond : ∀ i ∈ Finset.Icc 1 (N - n), ∃ j : Fin N, j ≠ l i ∧
      (∀ j' : Fin N, j' ≠ l i → scenCost h ω₀ ω (l i) j ≤ scenCost h ω₀ ω (l i) j') ∧
      j ∉ ((Finset.Icc 1 (N - n)).erase i).image l) :
    ∃ hL : ((Finset.Icc 1 (N - n)).image l)ᶜ.Nonempty,
      ((Finset.Icc 1 (N - n)).image l).card = N - n ∧
      IsLeast {x : ℝ | ∃ J : Finset (Fin N), ∃ hJ : Jᶜ.Nonempty, J.card = N - n ∧
          x = reductionCost (scenCost h ω₀ ω) p J hJ}
        (reductionCost (scenCost h ω₀ ω) p ((Finset.Icc 1 (N - n)).image l) hL) := by sorry

end ScenarioReduction.ForwardSelection
