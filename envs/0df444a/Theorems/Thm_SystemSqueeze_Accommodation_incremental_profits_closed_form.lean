-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_incremental_profits_closed_form
-- name    : SystemSqueeze.Accommodation.incremental_profits_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:22.388044+00:00
-- url     : https://prove2.me/theorems/a3bce677-8f51-4431-8679-eac928314dab
-- title:
--   Proof of Proposition 3, p. 36 — ΔΠ_A^X = γU_I(U_C − γU_I)/(18(1−γ)(1+γ)) and ΔΠ_A^Y = γ(U_I − γU_C)(3U_I − 2U_C)/(18(1−γ)(1+γ)) (corrected)
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, and fix Nash equilibrium price profiles of the no-entry and the accommodation subgames. Then $A$'s incremental profits from squeezing and from conversion are
--   $$\Delta\Pi_A^X=\frac{\gamma U_I(U_C-\gamma U_I)}{18(1-\gamma)(1+\gamma)},\qquad \Delta\Pi_A^Y=\frac{\gamma(U_I-\gamma U_C)(3U_I-2U_C)}{18(1-\gamma)(1+\gamma)}.$$
--
--   These closed forms are the input to the comparison in Proposition 3.
--
--   **Formalization Note** The paper prints $\Delta\Pi_A^Y=\gamma U_I(U_I-\gamma U_C)(2U_C-3U_I)/[18(1-\gamma)(1+\gamma)]$, with an extra factor $U_I$ and the opposite sign. Substituting the equilibrium values the paper lists in the same sentence into the definition of $\Delta\Pi_A^Y$ gives the expression above, and the paper's next display ($\Delta\Pi_A^X-\Delta\Pi_A^Y$) agrees with it. Example: at $U_C=5$, $U_I=4.2$, $\gamma=0.5$ the corrected form gives $0.16$, the printed one $-0.69$.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 36 (PDF 37), proof of Proposition 3

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proof of Proposition 3, p. 36: at the equilibria of the no-entry and accommodation
subgames, `ΔΠ_A^X = γUI(UC − γUI)/(18(1−γ)(1+γ))` and
`ΔΠ_A^Y = γ(UI − γUC)(3UI − 2UC)/(18(1−γ)(1+γ))` (the printed `ΔΠ_A^Y` carries an extra
factor `UI` and the opposite sign; this is the value the stated equilibrium quantities give). -/
theorem incremental_profits_closed_form (UC UI γ : ℝ) (h : Standing UC UI γ)
    (n : NoEntryPrices) (a : AccPrices) (hn : IsNoEntryEq UC n) (ha : IsAccEq UC UI γ a) :
    dPiX UC UI γ n a = γ * UI * (UC - γ * UI) / (18 * (1 - γ) * (1 + γ)) ∧
    dPiY UC UI γ n a = γ * (UI - γ * UC) * (3 * UI - 2 * UC) / (18 * (1 - γ) * (1 + γ)) := by sorry

end SystemSqueeze.Accommodation
