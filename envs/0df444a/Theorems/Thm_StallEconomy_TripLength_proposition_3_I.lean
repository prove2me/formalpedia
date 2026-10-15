-- Prove2me | Theorems.Thm_StallEconomy_TripLength_proposition_3_I
-- name    : StallEconomy.TripLength.proposition_3_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:51.949388+00:00
-- url     : https://prove2.me/theorems/6aa3be5c-0e6e-4253-940d-a827f924ad94
-- title:
--   Proposition 3(I), p. 18 — 𝔼[L_r] = (7√2R³ − 22R²r + 2√2Rr² + 12r³)/(15R²)
-- statement:
--   Let $R>0$ be the Euclidean edge length of the diamond service zone $\mathcal Z_R$ and $0\le r\le R/\sqrt2$ the customers' maximal walking distance. Let the stall $A$ be uniform on the inner diamond $\mathcal I_{R,r}$ (edge length $R-\sqrt2 r$), the next customer $B$ uniform on $\mathcal Z_R$, independently, and let $L_r = \max\{|A-B|-r,0\}$ be the stall's repositioning trip length in the Manhattan metric. Then
--
--   $$\mathbb E[L_r] = \frac{7\sqrt2\,R^3-22R^2r+2\sqrt2\,Rr^2+12r^3}{15R^2}.$$
--
--   At $r=0$ this is $7\sqrt2R/15$, the door-to-door mean of Proposition 1; at $r=R/\sqrt2$ it is $0$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 18, Proposition 3(I) (proof pp. 49–50)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem proposition_3_I (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    meanL R r = (7 * Real.sqrt 2 * R ^ 3 - 22 * R ^ 2 * r + 2 * Real.sqrt 2 * R * r ^ 2 + 12 * r ^ 3) / (15 * R ^ 2) := by sorry

end StallEconomy.TripLength
