-- Prove2me | Theorems.Thm_StallEconomy_TripLength_within_radius_second_moment
-- name    : StallEconomy.TripLength.within_radius_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:21.726646+00:00
-- url     : https://prove2.me/theorems/e34c1e24-eefc-4091-b62b-eeeee31912cd
-- title:
--   Proof of Proposition 3(II), p. 51 — 𝔼[L′₀²; L′₀ ≤ r] = ½r² · 2r²/R²
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$, with the stall $A$ uniform on the inner diamond $\mathcal I_{R,r}$, the customer $B$ uniform on the zone $\mathcal Z_R$, independently, and $L_0' = |A-B|$ their Manhattan distance. Then
--
--   $$\mathbb E\big[(L_0')^2\,\mathbf 1\{L_0'\le r\}\big] = \frac12\,r^2\cdot\frac{2r^2}{R^2}.$$
--
--   This is the product $\mathbb E[(L_0')^2\mid L_0'\le r]\,\mathbb P(L_0'\le r)$ with $\mathbb E[(L_0')^2\mid L_0'\le r] = \tfrac12 r^2$, the term subtracted in the variance computation for $L_r$.
--
--   **Formalization Note.** As for the first moment, the truncated expectation replaces the conditional one, which is undefined at $r=0$. The paper prints the conditioning event as "$L_0'^2\le r$"; the event meant, and used in the next display, is $L_0'\le r$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 51, proof of Proposition 3, part (II): 𝔼[L₀′²|L₀′² ⩽ r] = ½r² (conditioning event printed as L₀′² ⩽ r for L′₀ ⩽ r)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem within_radius_second_moment (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then l1 a b ^ 2 else 0) = (1 / 2) * r ^ 2 * (2 * r ^ 2 / R ^ 2) := by sorry

end StallEconomy.TripLength
