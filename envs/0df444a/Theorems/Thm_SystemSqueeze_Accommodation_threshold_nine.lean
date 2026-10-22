-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_threshold_nine
-- name    : SystemSqueeze.Accommodation.threshold_nine
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:32.465422+00:00
-- url     : https://prove2.me/theorems/951c82bc-0e91-433a-8d1b-ff4cda416ece
-- title:
--   Proof of Proposition 3, p. 37 — (8) ⇔ (9): γ ≥ U_C U_I/(2U_C² − U_I²), and this threshold lies below the admissible bound
-- statement:
--   Let $0<U_I<U_C$ and $0<\gamma<1$. Then inequality (8),
--   $$\frac{(U_C-\gamma U_I)(2U_C+\gamma U_I)}{18(1+\gamma)(1-\gamma)}\ \ge\ \frac{U_C^2}{9},$$
--   holds if and only if (9),
--   $$\gamma\ \ge\ \frac{U_CU_I}{2U_C^2-U_I^2},$$
--   holds. Moreover the threshold in (9) is strictly smaller than the upper end $(\sqrt{U_C^2+3U_I^2}-U_C)/U_I$ of the admissible range.
--
--   The second part shows that the range of $\gamma$ in which (9) holds is a nonempty part of the admissible range.
--
--   **Formalization Note** The hypothesis $U_I<U_C$ guarantees $2U_C^2-U_I^2>0$, so the division in (9) is a genuine one.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 37 (PDF 38), proof of Proposition 3, (8)–(9)

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- Proof of Proposition 3, p. 37: for `0 < UI < UC` and `0 < γ < 1`, inequality (8),
`(UC − γUI)(2UC + γUI)/(18(1+γ)(1−γ)) ≥ UC²/9`, is equivalent to (9),
`γ ≥ UC·UI/(2UC² − UI²)`, and this threshold lies strictly below the upper bound
`(√(UC² + 3UI²) − UC)/UI` of the admissible range. -/
theorem threshold_nine (UC UI γ : ℝ) (hUI : 0 < UI) (hlt : UI < UC) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) :
    ((UC - γ * UI) * (2 * UC + γ * UI) / (18 * (1 + γ) * (1 - γ)) ≥ UC ^ 2 / 9 ↔
        γ ≥ UC * UI / (2 * UC ^ 2 - UI ^ 2)) ∧
      UC * UI / (2 * UC ^ 2 - UI ^ 2) < gammaMax UC UI := by sorry

end SystemSqueeze.Accommodation
