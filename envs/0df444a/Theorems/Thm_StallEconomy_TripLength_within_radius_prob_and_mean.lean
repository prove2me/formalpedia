-- Prove2me | Theorems.Thm_StallEconomy_TripLength_within_radius_prob_and_mean
-- name    : StallEconomy.TripLength.within_radius_prob_and_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:55.81662+00:00
-- url     : https://prove2.me/theorems/a5139905-1156-4298-b344-1684dc6650b0
-- title:
--   Proof of Proposition 3(I), p. 50 — ℙ(L′₀ ≤ r) = 2r²/R² and 𝔼[L′₀; L′₀ ≤ r] = (2/3)r · 2r²/R²
-- statement:
--   Let $R>0$ and $0\le r\le R/\sqrt2$, with the stall $A$ uniform on the inner diamond $\mathcal I_{R,r}$, the customer $B$ uniform on the zone $\mathcal Z_R$, independently, and $L_0' = |A-B|$ their Manhattan distance. Then
--
--   $$\mathbb P(L_0'\le r) = \frac{2r^2}{R^2}, \qquad \mathbb E\big[L_0'\,\mathbf 1\{L_0'\le r\}\big] = \frac23\,r\cdot\frac{2r^2}{R^2}.$$
--
--   The second identity is the product $\mathbb E[L_0'\mid L_0'\le r]\,\mathbb P(L_0'\le r)$ with $\mathbb E[L_0'\mid L_0'\le r] = \tfrac23 r$, which is how the paper uses it. Together they give the decomposition $\mathbb E[L_0'] = \mathbb E[L_0'\mid L_0'>r](1-2r^2/R^2) + \tfrac23 r\cdot 2r^2/R^2$ that leads to Proposition 3(I).
--
--   **Formalization Note.** The statement uses unconditional (truncated) expectations rather than conditional ones, which would be undefined at $r=0$, where $\mathbb P(L_0'\le r)=0$. The paper prints $\mathbb P(L_0>r) = 1-2r^2/R^2$; the distance meant is $L_0'$ (the stall is in the inner diamond), and the statement is its complement $\mathbb P(L_0'\le r) = 2r^2/R^2$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 50, proof of Proposition 3, part (I): 𝔼[L′₀|L′₀ ⩽ r] = (2/3)r and ℙ(L₀ > r) = 1 − 2r²/R² (printed L₀ for L′₀)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem within_radius_prob_and_mean (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => if l1 a b ≤ r then 1 else 0) = 2 * r ^ 2 / R ^ 2 ∧
      E R r (fun a b => if l1 a b ≤ r then l1 a b else 0) = (2 / 3) * r * (2 * r ^ 2 / R ^ 2) := by sorry

end StallEconomy.TripLength
