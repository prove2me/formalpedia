-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_accommodation_profit_split
-- name    : SystemSqueeze.Accommodation.accommodation_profit_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:22.88092+00:00
-- url     : https://prove2.me/theorems/b867f1aa-14b6-4dec-8fbe-a70755570e14
-- title:
--   Proof of Proposition 3, p. 37 — A's accommodation profit splits into component profit (U_C − γU_I)(2U_C + γU_I)/(18(1+γ)(1−γ)) and integrated profit
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, and fix a Nash equilibrium of the accommodation subgame. Then $A$'s profit from its component and from its integrated system are
--   $$P_{C_A}^{(ii)}Q_C^{(ii)}=\frac{(U_C-\gamma U_I)(2U_C+\gamma U_I)}{18(1+\gamma)(1-\gamma)},\qquad P_{I_A}^{(ii)}Q_{I_A}^{(ii)}=\frac{U_I\big(3U_I-\gamma(2U_C+\gamma U_I)\big)}{12(1+\gamma)(1-\gamma)},$$
--   both gross of the investment $K$; they sum to $\Pi_A^{(ii)}$.
--
--   Comparing the component profit alone with the no-entry profit $U_C^2/9$ is how the paper shows that $A$ may enter with a loss-making integrated system.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 37 (PDF 38), proof of Proposition 3

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proof of Proposition 3, p. 37: at the accommodation equilibrium, `A`'s profit splits into
the component profit `(UC − γUI)(2UC + γUI)/(18(1+γ)(1−γ))` and the integrated-system profit
`UI(3UI − γ(2UC + γUI))/(12(1+γ)(1−γ))` (both gross of `K`). -/
theorem accommodation_profit_split (UC UI γ : ℝ) (h : Standing UC UI γ)
    (a : AccPrices) (ha : IsAccEq UC UI γ a) :
    componentProfitA UC UI γ a =
        (UC - γ * UI) * (2 * UC + γ * UI) / (18 * (1 + γ) * (1 - γ)) ∧
      integratedProfitA UC UI γ a =
        UI * (3 * UI - γ * (2 * UC + γ * UI)) / (12 * (1 + γ) * (1 - γ)) := by sorry

end SystemSqueeze.Accommodation
