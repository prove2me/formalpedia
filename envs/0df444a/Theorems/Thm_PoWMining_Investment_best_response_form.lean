-- Prove2me | Theorems.Thm_PoWMining_Investment_best_response_form
-- name    : PoWMining.Investment.best_response_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:30.453805+00:00
-- url     : https://prove2.me/theorems/28de8ec5-e2b5-484c-9c4f-1dadf5960d7b
-- title:
--   p. 44, proof of Proposition 5.1 — at every equilibrium investment, active miners invest min{1/η,1} and inactive miners invest 0
-- statement:
--   Consider the investment game under its standing assumptions, with $h^*$ any mining-equilibrium selection (for every $\beta\in[0,1]^N$, $h^*(\beta)$ is an equilibrium hash rate profile at costs $c_i(\beta_i)$). Let $\beta^*$ be an equilibrium investment and $A(\beta^*)$ the set of miners active at $h^*(\beta^*)$. Then for every miner $i$
--
--   $$
--   \beta^*_i=\begin{cases}\min\{1/\eta,1\}, & i\in A(\beta^*),\\ 0, & i\notin A(\beta^*).\end{cases}
--   $$
--
--   This is the first step of the proof of Proposition 5.1: active miners minimize their own cost, and an inactive miner gains nothing from investing.
--
--   **Formalization Note** The paper's "$i\in A(\beta^*_i)$" is read as $i\in A(\beta^*)$. $\min\{1/\eta,1\}$ is $1$ when $\eta=0$. The statement holds for every equilibrium investment, not only for those of the threshold form (5.1).
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 44, proof of Proposition 5.1

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

namespace PoWMining.Investment

/-- Proof of Proposition 5.1, p. 44: every equilibrium investment `β*` has
`β*_i = min{1/η, 1}` for the miners active at `β*` and `β*_i = 0` for the inactive ones. -/
theorem best_response_form {N : ℕ} (P : InvParams N) (hP : P.Standing)
    (hstar : (Fin N → ℝ) → Fin N → ℝ) (hsel : IsSelection P hstar) :
    ∀ β : Fin N → ℝ, IsInvEq P hstar β →
      ∀ i, β i = if i ∈ active hstar β then betaBar P else 0 := by sorry

end PoWMining.Investment
