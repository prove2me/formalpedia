-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_7
-- name    : PermBlockchain.Failure.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:25.9475+00:00
-- url     : https://prove2.me/theorems/8c7cfb7e-890e-49fc-bd0c-2f16b53e433a
-- title:
--   Proposition 4.7, p. 19 — neither full nor partial adoption is an equilibrium
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions. In the adoption game (8), where manufacturer $i$ chooses $a_i\in\{0,1\}$ and receives
--   $$\Pi(a_i,a_{-i})-\chi_i a_i ,$$
--   neither the full adoption profile ($a_i=1$ for all $i$) nor the partial adoption profile ($a_i=1$ exactly when $\xi_i=h$) is a pure Nash equilibrium.
--
--   Because price competition leaves no gross profit to recoup the adoption cost, an adopter always gains by withdrawing. This is the equilibrium half of the adoption failure of Proposition 4.8.
--
--   **Formalization Note** The gross profit $\Pi$ is the constant $0$ in every subgame, the outcome of Proposition A.1 used in the paper's proof (p. 36); the signalling and pricing game behind Proposition A.1 is not formalized. Equilibrium is `AGT.IsPureNash` over unilateral switches of $a_i$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 19, Proposition 4.7

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

/-- **Proposition 4.7** (p. 19): neither full nor partial adoption is an equilibrium of the
adoption game (8). -/
theorem proposition_4_7 {m : ℕ} (M : Model m) (hM : M.Standing) :
    ¬ M.IsEquilibrium Scenario.F.profile ∧ ¬ M.IsEquilibrium Scenario.P.profile := by sorry

end PermBlockchain.Failure
