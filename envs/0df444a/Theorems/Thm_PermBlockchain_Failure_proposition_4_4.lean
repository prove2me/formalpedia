-- Prove2me | Theorems.Thm_PermBlockchain_Failure_proposition_4_4
-- name    : PermBlockchain.Failure.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:39.186604+00:00
-- url     : https://prove2.me/theorems/4bf4b146-eb21-46a3-bf10-a901776e081e
-- title:
--   Proposition 4.4, p. 17 — vendor welfare: $W^F_V, W^P_V < W^N_V$
-- statement:
--   Consider the reduced-form blockchain supply chain under its standing assumptions, with $H=L+\Delta$ for some $\Delta>0$, and suppose Assumption 1 holds at $\Delta$. The vendor welfare
--   $$W_V^X=(\Psi_h s^X_h-\gamma s^X_h)+(\Psi^X_l s^X_l-c_l(s^X_l))$$
--   in the three scenarios satisfies
--   $$W^F_V<W^N_V\qquad\text{and}\qquad W^P_V<W^N_V .$$
--
--   Adoption reveals the low type goods, whose manufacturers cut the price they pay the low type vendor; the vendors lose from adoption.
--
--   **Formalization Note** Prices and shares are Proposition A.1's closed forms, with $(c_l')^{-1}(x)=\sup\{s\ge0:c_l'(s)\le x\}$, which is $0$ below $c_l'(0)$ as on p. 28. No second derivative of $c_l$ is assumed (the printed proof uses $c_l''$; the statement does not need it).
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 17, Proposition 4.4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace PermBlockchain.Failure

/-- **Proposition 4.4** (p. 17): vendor welfare satisfies `W^F_V, W^P_V < W^N_V`. -/
theorem proposition_4_4 {m : ℕ} (M : Model m) (hM : M.Standing) (Δ : ℝ) (hΔ : 0 < Δ)
    (hA : M.Assumption1 Δ) :
    M.WV .F Δ < M.WV .N Δ ∧ M.WV .P Δ < M.WV .N Δ := by sorry

end PermBlockchain.Failure
