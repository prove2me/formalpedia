-- Prove2me | Theorems.Thm_StallEconomy_TripLength_proposition_1
-- name    : StallEconomy.TripLength.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:25.012723+00:00
-- url     : https://prove2.me/theorems/3d816ff7-32cc-4649-80f3-3c30ece2fdb9
-- title:
--   Proposition 1, p. 11 — door-to-door trip length: 𝔼[L₀] = 7√2R/15 and Var(L₀) = 22R²/225
-- statement:
--   Let $R>0$ and let $A$, $B$ be two independent points, each uniformly distributed on the diamond service zone $\mathcal Z_R = \{|x|+|y|\le R/\sqrt2\}$ of Euclidean edge length $R$. The door-to-door repositioning trip length is their Manhattan distance $L_0 = |A-B| = |a_1-b_1|+|a_2-b_2|$. Then
--
--   $$\mathbb E[L_0] = \frac{7\sqrt2\,R}{15}, \qquad \operatorname{Var}(L_0) = \mathbb E[L_0^2]-\mathbb E[L_0]^2 = \frac{22R^2}{225}.$$
--
--   In the paper $R = R(\rho) = 1/\sqrt\rho$ for stall density $\rho$. This is the special case $r=0$ of Proposition 3, and the mean and variance feed the M/G/1 waiting-time formula of the door-to-door service mode.
--
--   **Formalization Note.** The expectation is `E R 0`, under which the stall's scale factor is $1$, so both points are uniform on the zone; the statement is for every $R>0$ rather than for a stall density $\rho$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 11, Proposition 1 (proof pp. 44–45)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem proposition_1 (R : ℝ) (hR : 0 < R) :
    E R 0 l1 = 7 * Real.sqrt 2 * R / 15 ∧
      E R 0 (fun a b => l1 a b ^ 2) - E R 0 l1 ^ 2 = 22 * R ^ 2 / 225 := by sorry

end StallEconomy.TripLength
