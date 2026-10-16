-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_exists_poa_ne_same_demand
-- name    : SensitivityPoA.NoUniform.exists_poa_ne_same_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:01.084772+00:00
-- url     : https://prove2.me/theorems/3508c34a-013f-4a9b-a884-d328dabd9b2c
-- title:
--   p. 24 — there are two games with the same demand vector and different prices of anarchy
-- statement:
--   Let $(G, K, S)$ satisfy the standing assumptions (in particular $|S_k| \ge 2$ for every O/D pair $k$, Condition 1) and the antichain condition (no path of a pair is contained in another path of the same pair). Then there exist two games $\Gamma = (\tau, d)$ and $\Gamma' = (\sigma, d')$ of the game space $\mathcal G(G,K,S)$ with
--   $$d = d' \qquad\text{and}\qquad \rho(\Gamma) \neq \rho(\Gamma').$$
--
--   This is the existence claim on which the proof of Theorem 8a) rests: some demand slice $\mathcal G(G,K,S)|_d$ contains two games with different prices of anarchy.
--
--   **Formalization Note.** The antichain condition is an added hypothesis: it holds for the loop-free paths of G2, but routes here are arbitrary $0/1$ incidence columns, and with $S_k = \{\{a\},\{a,b\}\}$ every game has $\rho = 1$ and the claim fails. The statement is existential in the demand vector, as on the page ("there are indeed such two games in the demand slice").
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 24, §4.1, second paragraph (two games with ρ(Γ) ≠ ρ(Γ′) and d = d′)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem exists_poa_ne_same_demand (N : Network) (hN : N.Standing) (hA : N.Antichain) :
    ∃ Γ ∈ gameSpace N, ∃ Γ' ∈ gameSpace N, Γ.d = Γ'.d ∧ PoA Γ ≠ PoA Γ' := by sorry

end SensitivityPoA.NoUniform
