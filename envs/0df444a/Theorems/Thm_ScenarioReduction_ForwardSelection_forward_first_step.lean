-- Prove2me | Theorems.Thm_ScenarioReduction_ForwardSelection_forward_first_step
-- name    : ScenarioReduction.ForwardSelection.forward_first_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:58:33.732482+00:00
-- url     : https://prove2.me/theorems/04fd0904-3e81-4599-84a5-2f8a019cf03d
-- title:
--   Eq. (10) — keeping one scenario $u$ costs $\sum_{i=1}^N p_i c(\omega_i,\omega_u)$
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be scenarios with probabilities $p_i>0$, $\sum_ip_i=1$, and let $c$ be the cost (3). Deleting all scenarios but $u$, i.e. $J=\{1,\dots,N\}\setminus\{u\}$, has reduction cost
--   $$
--   D_{\{1,\dots,N\}\setminus\{u\}}=\sum_{i=1}^Np_i\,c(\omega_i,\omega_u),
--   $$
--   and consequently the values of problem (8) for $\#J=N-1$ are exactly the values of problem (10):
--   $$
--   \bigl\{D_J:\#J=N-1\bigr\}=\Bigl\{\sum_{i=1}^Np_i\,c(\omega_i,\omega_u):u\in\{1,\dots,N\}\Bigr\},
--   $$
--   so that (8) with $\#J=N-1$ takes the form $\min_{u\in\{1,\dots,N\}}\sum_{i=1}^Np_ic(\omega_i,\omega_u)$.
--
--   This is the first step of forward selection: the first kept scenario minimizes the expected cost to all scenarios.
--
--   **Formalization Note** The sum runs over all $i$, including $i=u$, as printed; the term $i=u$ vanishes because $c(\omega,\omega)=0$ for the cost (3).
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 191, eq. (10)

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost

namespace ScenarioReduction.ForwardSelection

/-- Eq. (10), Heitsch–Römisch 2003, p. 191. Keeping a single scenario `u` (deleting
`J = {1..N} ∖ {u}`) costs `D_J = ∑_{i=1}^N pᵢ c(ωᵢ, ω_u)`, and the values of problem (8) with
`#J = N − 1` are exactly the values `∑ᵢ pᵢ c(ωᵢ, ω_u)`, `u = 1..N`, of problem (10). -/
theorem forward_first_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    (∀ u : Fin N, reductionCost (scenCost h ω₀ ω) p (Finset.univ.erase u)
        (compl_erase_nonempty _ _) = ∑ i, p i * scenCost h ω₀ ω i u) ∧
    {x : ℝ | ∃ J : Finset (Fin N), ∃ hJ : Jᶜ.Nonempty, J.card = N - 1 ∧
        x = reductionCost (scenCost h ω₀ ω) p J hJ} =
      Set.range (fun u : Fin N => ∑ i, p i * scenCost h ω₀ ω i u) := by sorry

end ScenarioReduction.ForwardSelection
