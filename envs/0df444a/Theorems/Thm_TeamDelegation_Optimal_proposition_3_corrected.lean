-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_proposition_3_corrected
-- name    : TeamDelegation.Optimal.proposition_3_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:17.048342+00:00
-- url     : https://prove2.me/theorems/6611f369-c9db-498d-9074-c6d216341c6f
-- title:
--   Proposition 3 (corrected for limited liability): delegated implementation
-- statement:
--   Suppose $\widehat\Delta_A<\Delta_A<\Delta_A^{\max}$ and $\Delta_B<\Delta_B^{\max}$. With adoption-cost differences $\Delta_A,\Delta_B$, the piecewise success bonus $w_A^{\mathrm{del}}$ of equation (21) and the success bonus $w_B^{\mathrm{del}}$ of equation (23) implement both agents working and the correct production method under delegation, provided $w_B^{\mathrm{del}}\ge0$:
--
--   $$\operatorname{Implements}_{\mathrm{del}}(w_A^{\mathrm{del}},w_B^{\mathrm{del}}).$$
--
--   The theorem supplies the delegated implementation needed for the strict-cost and collusion result.
--
--   **Formalization Note** The nonnegative-wage guard corrects the printed Proposition 3: its unrestricted lower range for $\Delta_B$ can make equation (23) negative, contrary to the paper's limited-liability assumption. The other additions, $0\le r<1$ and probability endpoints, are standing assumptions of the formal model.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 18 (PDF 19), Proposition 3, equations (21)–(23); limited-liability condition on p. 8 (PDF 9)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Proposition 3, p. 18, with the limited-liability correction
`0 ≤ wdelB`: an arbitrarily negative ΔB otherwise makes the printed wage negative. -/
theorem proposition_3_corrected (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B ΔA ΔB : ℝ)
    (hAlo : DeltaHatA P < ΔA) (hAhi : ΔA < DeltaMaxA P)
    (hBhi : ΔB < DeltaMaxB P) (hBnonneg : 0 ≤ wdelB P ΔB) :
    Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
      (wdelA P ΔA) (wdelB P ΔB) := by sorry

end TeamDelegation.Optimal
