-- Prove2me | Theorems.Thm_StallEconomy_TripLength_expected_l1
-- name    : StallEconomy.TripLength.expected_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:18.712629+00:00
-- url     : https://prove2.me/theorems/61944d23-5753-4f06-b275-6a54c6171eb1
-- title:
--   Proof of Proposition 3(I), p. 49 — 𝔼[L′₀] = 7√2R/15 − 7r/15 + 2√2r²/(15R) + 2r³/(15R²)
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$. Let the stall $A$ be uniform on the inner diamond $\mathcal I_{R,r} = \{|x|+|y|\le R/\sqrt2-r\}$ and the customer $B$ uniform on the zone $\mathcal Z_R = \{|x|+|y|\le R/\sqrt2\}$, independently, and let $L_0' = |A-B|$ be their Manhattan distance. Then
--
--   $$\mathbb E[L_0'] = \frac{7\sqrt2\,R}{15} - \frac{7r}{15} + \frac{2\sqrt2\,r^2}{15R} + \frac{2r^3}{15R^2}.$$
--
--   This is the mean distance before the customer's walk is subtracted; Proposition 3(I) is obtained from it by removing the contribution of the event $L_0'\le r$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 49, proof of Proposition 3, part (I), display for 𝔼[L′₀]

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem expected_l1 (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r l1 = 7 * Real.sqrt 2 * R / 15 - 7 * r / 15 + 2 * Real.sqrt 2 * r ^ 2 / (15 * R)
      + 2 * r ^ 3 / (15 * R ^ 2) := by sorry

end StallEconomy.TripLength
