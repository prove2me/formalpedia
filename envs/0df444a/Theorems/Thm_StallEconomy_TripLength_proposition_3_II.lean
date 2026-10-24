-- Prove2me | Theorems.Thm_StallEconomy_TripLength_proposition_3_II
-- name    : StallEconomy.TripLength.proposition_3_II
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:02.800247+00:00
-- url     : https://prove2.me/theorems/0110a14c-eebc-48cd-bbab-9c8628311611
-- title:
--   Proposition 3(II), p. 18 — Var(L_r) in closed form
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$. Let the stall $A$ be uniform on the inner diamond $\mathcal I_{R,r}$, the next customer $B$ uniform on the zone $\mathcal Z_R$, independently, and $L_r = \max\{|A-B|-r,0\}$ the repositioning trip length in the Manhattan metric. Then
--
--   $$\operatorname{Var}(L_r) = \frac{22R^6-22\sqrt2\,R^5r-140\sqrt2\,R^3r^3+400R^2r^4-48\sqrt2\,Rr^5-144r^6}{225R^4}.$$
--
--   At $r=0$ this is $22R^2/225$, the door-to-door variance of Proposition 1; at $r=R/\sqrt2$ it is $0$. Together with the mean it determines the second moment of the service time in the paper's M/G/1 waiting-time formula.
--
--   **Formalization Note.** The variance is $\mathbb E[L_r^2]-\mathbb E[L_r]^2$ under the same law, as defined on p. 51 of the paper.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 18, Proposition 3(II) (proof pp. 50–51)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem proposition_3_II (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    varL R r = (22 * R ^ 6 - 22 * Real.sqrt 2 * R ^ 5 * r - 140 * Real.sqrt 2 * R ^ 3 * r ^ 3 + 400 * R ^ 2 * r ^ 4
      - 48 * Real.sqrt 2 * R * r ^ 5 - 144 * r ^ 6) / (225 * R ^ 4) := by sorry

end StallEconomy.TripLength
