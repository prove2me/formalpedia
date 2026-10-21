-- Prove2me | Theorems.Thm_StallEconomy_TripLength_second_moment_X
-- name    : StallEconomy.TripLength.second_moment_X
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:23.046583+00:00
-- url     : https://prove2.me/theorems/4c45ad69-b382-49f1-bbed-65af49c606f3
-- title:
--   Proof of Proposition 3(II), p. 50 — 𝔼[X²] = (R² − √2Rr + r²)/6
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$, with the stall $A=(X_1,Y_1)$ uniform on the inner diamond $\mathcal I_{R,r}$ and the customer $B=(X_2,Y_2)$ uniform on the zone $\mathcal Z_R$, independently. Let $X = |X_1-X_2|$ be the horizontal component of their Manhattan distance. Then
--
--   $$\mathbb E[X^2] = \frac{R^2-\sqrt2\,Rr+r^2}{6}.$$
--
--   By symmetry $\mathbb E[Y^2]$ is the same, and together with $\mathbb E[XY]$ this gives the second moment of $L_0' = X+Y$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 50, proof of Proposition 3, part (II), display for 𝔼[X²]

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem second_moment_X (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => (a.1 - b.1) ^ 2) = (R ^ 2 - Real.sqrt 2 * R * r + r ^ 2) / 6 := by sorry

end StallEconomy.TripLength
