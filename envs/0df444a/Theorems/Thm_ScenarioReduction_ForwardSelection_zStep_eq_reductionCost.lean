-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_zStep_eq_reductionCost
-- name    : ScenarioReduction.ForwardSelection.zStep_eq_reductionCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:01:13.657147+00:00
-- url     : https://prove2.me/theorems/2aa4570e-19e3-4460-b194-d1d44f4d1df9
-- title:
--   Eq. (17), conclusion — $z^{[i]}_u=D_{J^{[i-1]}\setminus\{u\}}$ for every $u\in J^{[i-1]}$
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be scenarios with probabilities $p_i>0$, $\sum_ip_i=1$, $c$ the cost (3), and $u_1,u_2,\dots$ any sequence of indices, with $J^{[i]}$, $c^{[i]}$ and $z^{[i]}$ as in Algorithm 2.4. For every step $i\ge 1$ and every $u\in J^{[i-1]}$,
--   $$
--   z^{[i]}_u=\sum_{k\in J^{[i-1]}\setminus\{u\}}p_k\min_{j\notin J^{[i-1]}\setminus\{u\}}c(\omega_k,\omega_j)=D_{J^{[i-1]}\setminus\{u\}} .
--   $$
--
--   Hence the objective minimized in each step of Algorithm 2.4 coincides with the objective of the forward selection principle (16), which is the content of the chain (17).
--
--   **Formalization Note** No run hypothesis is assumed: the identity holds for every sequence $u$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 194, proof of Theorem 2.5, eq. (17)

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun

namespace ScenarioReduction.ForwardSelection

/-- Eq. (17), Heitsch–Römisch 2003, p. 194 (last two lines). For any sequence `u`, any step
`i ≥ 1` and any `v ∈ J^{[i-1]}`, the quantity of Algorithm 2.4 is the reduction cost (8) of
deleting `J^{[i-1]} ∖ {v}`: `z^{[i]}_v = D_{J^{[i-1]} ∖ {v}}`. -/
theorem zStep_eq_reductionCost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (u : ℕ → Fin N) (i : ℕ) (hi : 1 ≤ i) (v : Fin N) (hv : v ∈ Jstep u (i - 1)) :
    zStep (scenCost h ω₀ ω) p u i v =
      reductionCost (scenCost h ω₀ ω) p ((Jstep u (i - 1)).erase v)
        (compl_erase_nonempty _ _) := by sorry

end ScenarioReduction.ForwardSelection
