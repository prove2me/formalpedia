-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_3
-- name    : PermBlockchain.Failure.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:25.722549+00:00
-- url     : https://prove2.me/theorems/8cc0986b-1cc5-42e1-952a-9151218bf5e9
-- title:
--   Proposition 4.3, p. 17 — manufacturer welfare: $W^F_M < W^P_M < W^N_M$
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions. The manufacturer welfare $W_M^X=\sum_{i\in M}(\Pi(a^X_i,a^X_{-i})-\chi_i a^X_i)$ in the full, partial and non-adoption scenarios satisfies
--   $$W^F_M\ <\ W^P_M\ <\ W^N_M .$$
--
--   Since price competition leaves every manufacturer with zero gross profit, adoption only adds the adoption costs $\chi_i$; the more manufacturers adopt, the lower their aggregate welfare.
--
--   **Formalization Note** The gross profit $\Pi$ is the constant $0$, the outcome of Proposition A.1 that the paper's proof of this proposition (p. 34) invokes; the paper's display (11) is read, as in that proof, at the scenario's fixed adoption profile.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 17, Proposition 4.3

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

/-- **Proposition 4.3** (p. 17): manufacturer welfare satisfies `W^F_M < W^P_M < W^N_M`. -/
theorem proposition_4_3 {m : ℕ} (M : Model m) (hM : M.Standing) :
    M.WM .F < M.WM .P ∧ M.WM .P < M.WM .N := by sorry

end PermBlockchain.Failure
