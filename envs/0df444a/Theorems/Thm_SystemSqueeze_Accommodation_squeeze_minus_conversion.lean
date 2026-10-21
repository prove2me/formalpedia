-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_squeeze_minus_conversion
-- name    : SystemSqueeze.Accommodation.squeeze_minus_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:15.042581+00:00
-- url     : https://prove2.me/theorems/65ed5b4b-6125-4f0d-9747-e12a424ae4e2
-- title:
--   Proof of Proposition 3, p. 36 — ΔΠ_A^X − ΔΠ_A^Y = γ(U_C − U_I)(U_I(3+γ) − 2γU_C)/(18(1−γ)(1+γ)), with U_I(3+γ) − 2γU_C > 0
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, including the admissible range, and fix Nash equilibrium price profiles of the no-entry and accommodation subgames. Then
--   $$\Delta\Pi_A^X-\Delta\Pi_A^Y=\frac{\gamma(U_C-U_I)\,\big(U_I(3+\gamma)-2\gamma U_C\big)}{18(1-\gamma)(1+\gamma)},$$
--   and the factor $U_I(3+\gamma)-2\gamma U_C$ is strictly positive.
--
--   Consequently the sign of $\Delta\Pi_A^X-\Delta\Pi_A^Y$ is the sign of $U_C-U_I$, which is the first sentence of Proposition 3 (i) and Proposition 3 (ii).
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 36 (PDF 37), proof of Proposition 3

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proof of Proposition 3, p. 36: at the equilibria of the no-entry and accommodation
subgames, `ΔΠ_A^X − ΔΠ_A^Y = γ(UC − UI)(UI(3+γ) − 2γUC)/(18(1−γ)(1+γ))`, and on the
admissible range the factor `UI(3+γ) − 2γUC` is strictly positive. -/
theorem squeeze_minus_conversion (UC UI γ : ℝ) (h : Standing UC UI γ)
    (n : NoEntryPrices) (a : AccPrices) (hn : IsNoEntryEq UC n) (ha : IsAccEq UC UI γ a) :
    dPiX UC UI γ n a - dPiY UC UI γ n a =
        γ * (UC - UI) * (UI * (3 + γ) - 2 * γ * UC) / (18 * (1 - γ) * (1 + γ)) ∧
      0 < UI * (3 + γ) - 2 * γ * UC := by sorry

end SystemSqueeze.Accommodation
