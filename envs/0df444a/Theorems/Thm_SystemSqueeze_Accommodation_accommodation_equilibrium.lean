-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_accommodation_equilibrium
-- name    : SystemSqueeze.Accommodation.accommodation_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:28.30239+00:00
-- url     : https://prove2.me/theorems/f3766007-e87e-47a2-b6c0-1b65c8108b6f
-- title:
--   §4.2 B, pp. 11–12 — the accommodation equilibrium: prices U_C/3 + γU_I/6, U_C/3 − γU_I/3, U_I/2 and profits Π_A^{(ii)}, Π_B^{(ii)}
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, and consider the subgame in which only $A$ has launched the integrated system. A price profile $(P_{C_A},P_{I_A},P_{C_B})$ is a Nash equilibrium (with $A$ choosing both its prices) if and only if
--   $$P_{C_A}=\frac{U_C}{3}+\frac{\gamma U_I}{6},\qquad P_{C_B}=\frac{U_C}{3}-\frac{\gamma U_I}{3},\qquad P_{I_A}=\frac{U_I}{2}.$$
--   At this equilibrium the profits, gross of $K$, are
--   $$\Pi_A^{(ii)}=\frac{U_I^2(9-5\gamma^2)+4U_C^2-8\gamma U_CU_I}{36(1+\gamma)(1-\gamma)},\qquad \Pi_B^{(ii)}=\frac{(U_C-\gamma U_I)^2}{9(1+\gamma)(1-\gamma)}.$$
--
--   Compared with no entry, $A$ raises its component price and $B$ lowers its own: this asymmetry is the squeezing effect studied in the mission.
--
--   **Formalization Note** The paper prints $\Pi_B^{(ii)}=(U_C-\gamma U_I)^2(1-\gamma)/[9(1+\gamma)(1-\gamma)]$, with a stray factor $(1-\gamma)$ in the numerator. The value stated here is $P_{C_B}^{(ii)}Q_C^{(ii)}$ at the printed prices, and it is the value the paper's own (3) is consistent with.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), pp. 11–12 (PDF 12–13), §4.2 B

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- §4.2 B, pp. 11–12: the unique price equilibrium of the accommodation subgame is
`P_{C_A} = UC/3 + γUI/6`, `P_{C_B} = UC/3 − γUI/3`, `P_{I_A} = UI/2`, with profits
`Π_A^{(ii)} = (UI²(9 − 5γ²) + 4UC² − 8γUCUI)/(36(1+γ)(1−γ))` and
`Π_B^{(ii)} = (UC − γUI)²/(9(1+γ)(1−γ))` (the printed `Π_B^{(ii)}` carries a stray factor
`(1 − γ)` in the numerator; this is the corrected value). -/
theorem accommodation_equilibrium (UC UI γ : ℝ) (h : Standing UC UI γ) (p : AccPrices) :
    (IsAccEq UC UI γ p ↔
      p.pCA = UC / 3 + γ * UI / 6 ∧ p.pCB = UC / 3 - γ * UI / 3 ∧ p.pIA = UI / 2) ∧
    (IsAccEq UC UI γ p →
      profitA1 UC UI γ p =
          (UI ^ 2 * (9 - 5 * γ ^ 2) + 4 * UC ^ 2 - 8 * γ * UC * UI) /
            (36 * (1 + γ) * (1 - γ)) ∧
        profitB1 UC UI γ p = (UC - γ * UI) ^ 2 / (9 * (1 + γ) * (1 - γ))) := by sorry

end SystemSqueeze.Accommodation
