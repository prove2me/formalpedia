-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_escalation_equilibrium
-- name    : SystemSqueeze.Accommodation.escalation_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:19.430001+00:00
-- url     : https://prove2.me/theorems/b814494e-a3e0-4129-820a-a625ccdaf4fa
-- title:
--   §4.2 C, pp. 12–13 — the escalation equilibrium: symmetric prices U_C/3 − γU_I/(3(2−γ)), U_I(1−γ)/(2−γ) and profit Π^{(iii)}
-- statement:
--   Let $U_C,U_I,\gamma$ satisfy the standing assumptions, and consider the subgame in which both complementors have launched integrated systems. A price profile $(P_{C_A},P_{I_A},P_{C_B},P_{I_B})$ is a Nash equilibrium (each firm choosing both its prices) if and only if, for $i=A,B$,
--   $$P_{C_i}=\frac{U_C}{3}-\frac{\gamma U_I}{3(2-\gamma)},\qquad P_{I_i}=\frac{U_I(1-\gamma)}{2-\gamma}.$$
--   At this equilibrium each firm earns, gross of $K$,
--   $$\Pi_A^{(iii)}=\Pi_B^{(iii)}=\frac{(U_C(2-\gamma)-\gamma U_I)(U_C(1+\gamma)-2\gamma U_I)}{9(1+2\gamma)(2-\gamma)(1-\gamma)}+\frac{U_I\,(U_I(3-2\gamma^2)-\gamma U_C(2-\gamma))}{3(1+2\gamma)(2-\gamma)^2}.$$
--
--   This profit enters $B$'s entry decision once $A$ is in, and so the lower entry threshold $\underline K$.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), pp. 12–13 (PDF 13–14), §4.2 C

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- §4.2 C, pp. 12–13: the unique price equilibrium of the escalation subgame is symmetric,
`P_{C_A} = P_{C_B} = UC/3 − γUI/(3(2−γ))` and `P_{I_A} = P_{I_B} = UI(1−γ)/(2−γ)`, and each
firm earns (gross of `K`)
`(UC(2−γ) − γUI)(UC(1+γ) − 2γUI)/(9(1+2γ)(2−γ)(1−γ)) + UI(UI(3−2γ²) − γUC(2−γ))/(3(1+2γ)(2−γ)²)`. -/
theorem escalation_equilibrium (UC UI γ : ℝ) (h : Standing UC UI γ) (p : EscPrices) :
    (IsEscEq UC UI γ p ↔
      p.pCA = UC / 3 - γ * UI / (3 * (2 - γ)) ∧ p.pCB = UC / 3 - γ * UI / (3 * (2 - γ)) ∧
        p.pIA = UI * (1 - γ) / (2 - γ) ∧ p.pIB = UI * (1 - γ) / (2 - γ)) ∧
    (IsEscEq UC UI γ p →
      profitA2 UC UI γ p =
          (UC * (2 - γ) - γ * UI) * (UC * (1 + γ) - 2 * γ * UI) /
              (9 * (1 + 2 * γ) * (2 - γ) * (1 - γ)) +
            UI * (UI * (3 - 2 * γ ^ 2) - γ * UC * (2 - γ)) / (3 * (1 + 2 * γ) * (2 - γ) ^ 2) ∧
        profitB2 UC UI γ p =
          (UC * (2 - γ) - γ * UI) * (UC * (1 + γ) - 2 * γ * UI) /
              (9 * (1 + 2 * γ) * (2 - γ) * (1 - γ)) +
            UI * (UI * (3 - 2 * γ ^ 2) - γ * UC * (2 - γ)) / (3 * (1 + 2 * γ) * (2 - γ) ^ 2)) := by sorry

end SystemSqueeze.Accommodation
