-- Prove2me | Theorems.Thm_StallEconomy_TripLength_expected_l1_sq
-- name    : StallEconomy.TripLength.expected_l1_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:54.70098+00:00
-- url     : https://prove2.me/theorems/440098f4-6bef-400a-9cda-a935e8cf829c
-- title:
--   Proof of Proposition 3(II), p. 51 — 𝔼[L′₀²] = (8R⁴ − 8√2R³r + 7R²r² + r⁴)/(15R²)
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$, with the stall $A$ uniform on the inner diamond $\mathcal I_{R,r}$, the customer $B$ uniform on the zone $\mathcal Z_R$, independently, and $L_0' = |A-B|$ their Manhattan distance. Then
--
--   $$\mathbb E\big[(L_0')^2\big] = \frac{8R^4-8\sqrt2\,R^3r+7R^2r^2+r^4}{15R^2}.$$
--
--   This second moment of the untruncated distance is the first term of the variance computation for $L_r$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 51, proof of Proposition 3, part (II), display for 𝔼(L′₀²)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem expected_l1_sq (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => l1 a b ^ 2)
      = (8 * R ^ 4 - 8 * Real.sqrt 2 * R ^ 3 * r + 7 * R ^ 2 * r ^ 2 + r ^ 4) / (15 * R ^ 2) := by sorry

end StallEconomy.TripLength
