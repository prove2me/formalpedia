-- Prove2me | Theorems.Thm_Teletriage_OneShot_dd_integral
-- name    : Teletriage.OneShot.dd_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:06.117835+00:00
-- url     : https://prove2.me/theorems/246ab5d4-f6e5-4138-89d0-8d213a1645ea
-- title:
--   Proof of Proposition 3, p. ec2 (PDF 27) — closed form of π^DD − π̃^DD under Uniform[l,u] beliefs
-- statement:
--   Under the hypotheses of Proposition 3 (standing assumptions, informative teletriage, beliefs uniform on $[l,u]\subseteq[0,1]$ with $\underline b_0<l<b_0<u<\bar b_0$), let $\pi^{DD}=\frac1{u-l}\int_l^u\pi^{DD}(s)\,ds$ and $\tilde\pi^{DD}=\frac1{u-l}\int_l^u\tilde\pi^{DD}(s)\,ds$ be the population double-dipping rates without and with teletriage. Then
--   $$\pi^{DD}-\tilde\pi^{DD}=\frac{b_0^2-l^2-\alpha\,(u^2-l^2)}{2(u-l)}.$$
--
--   This gives the second half of Proposition 3: the difference is positive exactly when $\alpha<\alpha^0$.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. ec2 (PDF 27), proof of Proposition 3

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proof of Proposition 3, p. ec2 ("analogous"): under the hypotheses of Proposition 3,
`π^DD − π̃^DD = (b0² − l² − α(u² − l²)) / (2(u − l))`. -/
theorem dd_integral (P : Params) (hS : P.Standing) (hI : P.Informative) (l u : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (h1 : bLow P < l) (h2 : l < b0 P) (h3 : b0 P < u) (h4 : u < bHigh P) :
    avg (piDD P) l u - avg (piDDtt P) l u =
      (b0 P ^ 2 - l ^ 2 - P.α * (u ^ 2 - l ^ 2)) / (2 * (u - l)) := by sorry

end Teletriage.OneShot
