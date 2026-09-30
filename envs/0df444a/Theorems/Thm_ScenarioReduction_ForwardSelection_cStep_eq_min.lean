-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_cStep_eq_min
-- name    : ScenarioReduction.ForwardSelection.cStep_eq_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:00:40.63177+00:00
-- url     : https://prove2.me/theorems/7c45219e-ba50-48d8-ab79-a464dd546acc
-- title:
--   Eq. (17), unrolled recursion — $c^{[i]}_{ku}=\min\{c^{[1]}_{ku},c^{[1]}_{ku_{i-1}},\dots,c^{[1]}_{ku_1}\}=\min_{j\notin J^{[i-1]}\setminus\{u\}}c(\omega_k,\omega_j)$
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be scenarios, $c$ the cost (3), and $u_1,u_2,\dots$ any sequence of indices, with $J^{[i]}=\{1,\dots,N\}\setminus\{u_1,\dots,u_i\}$ and $c^{[i]}$ the recursively updated cost matrices of Algorithm 2.4. For every step $i\ge 1$, every $u\in J^{[i-1]}$ and every $k$,
--   $$
--   c^{[i]}_{ku}=\min\bigl\{c^{[1]}_{ku},c^{[1]}_{ku_{i-1}},\dots,c^{[1]}_{ku_1}\bigr\}=\min_{j\notin J^{[i-1]}\setminus\{u\}}c(\omega_k,\omega_j).
--   $$
--
--   This is the step of the proof of Theorem 2.5 that unwinds the pairwise update of Algorithm 2.4 into the inner minimum of the forward selection principle (16).
--
--   **Formalization Note** No run hypothesis is assumed: the identity holds for every sequence $u$. The minimum on the right is `Finset.inf'` over the complement of $J^{[i-1]}\setminus\{u\}$, which is $\{u,u_1,\dots,u_{i-1}\}$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 194, proof of Theorem 2.5, eq. (17), lines 2–6

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun

namespace ScenarioReduction.ForwardSelection

/-- Eq. (17), Heitsch–Römisch 2003, p. 194 (the unrolled recursion). For any sequence `u`, any
step `i ≥ 1` and any `v ∈ J^{[i-1]}`, the recursively computed cost of Algorithm 2.4 is
`c^{[i]}_{kv} = min{c^{[1]}_{kv}, c^{[1]}_{k u_{i-1}}, …, c^{[1]}_{k u₁}} = min_{j ∉ J^{[i-1]} ∖ {v}} c(ωₖ, ωⱼ)`. -/
theorem cStep_eq_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (u : ℕ → Fin N) (i : ℕ) (hi : 1 ≤ i) (v : Fin N)
    (hv : v ∈ Jstep u (i - 1)) (k : Fin N) :
    cStep (scenCost h ω₀ ω) u i k v =
      ((Jstep u (i - 1)).erase v)ᶜ.inf' (compl_erase_nonempty _ _)
        (fun j => scenCost h ω₀ ω k j) := by sorry

end ScenarioReduction.ForwardSelection
