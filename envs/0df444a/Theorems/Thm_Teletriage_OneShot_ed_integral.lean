-- Prove2me | Theorems.Thm_Teletriage_OneShot_ed_integral
-- name    : Teletriage.OneShot.ed_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:20.585974+00:00
-- url     : https://prove2.me/theorems/6822775b-55b7-4621-b997-217cf62de07d
-- title:
--   Proof of Proposition 3, p. ec2 (PDF 27) — closed form of π^ED − π̃^ED under Uniform[l,u] beliefs, and positivity of the denominator of (15)
-- statement:
--   Assume the standing assumptions and informative teletriage, let beliefs be uniformly distributed on $[l,u]\subseteq[0,1]$, and assume $\underline b_0<l<b_0<u<\bar b_0$. Let $\pi^{ED}=\frac1{u-l}\int_l^u\pi^{ED}(s)\,ds$ and $\tilde\pi^{ED}=\frac1{u-l}\int_l^u\tilde\pi^{ED}(s)\,ds$ be the population ED usage rates without and with teletriage. Then
--   $$\pi^{ED}-\tilde\pi^{ED}=\frac{\bigl(u-\frac{u^2}{2}\bigr)-\bigl(b_0-\frac{b_0^2}{2}\bigr)-\beta\Bigl[\bigl(u-\frac{u^2}{2}\bigr)-\bigl(l-\frac{l^2}{2}\bigr)\Bigr]}{u-l},$$
--   and the denominator of (15) is positive: $\bigl(u-\frac{u^2}{2}\bigr)-\bigl(l-\frac{l^2}{2}\bigr)>0$.
--
--   Together these give the first half of Proposition 3: the difference is positive exactly when $\beta<\beta^0$.
--
--   **Formalization Note** The page prints the denominator of its intermediate fraction as $u-l-(\frac{u^2}{2}+\frac{l^2}{2})$; the correct denominator, the one of (15), is $u-l-(\frac{u^2}{2}-\frac{l^2}{2})$, which is what is stated.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. ec2 (PDF 27), proof of Proposition 3

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proof of Proposition 3, p. ec2: under the hypotheses of Proposition 3,
`π^ED − π̃^ED = [(u − u²/2) − (b0 − b0²/2) − β((u − u²/2) − (l − l²/2))]/(u − l)`, and the
denominator `(u − u²/2) − (l − l²/2)` of (15) is positive. -/
theorem ed_integral (P : Params) (hS : P.Standing) (hI : P.Informative) (l u : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (h1 : bLow P < l) (h2 : l < b0 P) (h3 : b0 P < u) (h4 : u < bHigh P) :
    avg (piED P) l u - avg (piEDtt P) l u =
      ((u - u ^ 2 / 2) - (b0 P - b0 P ^ 2 / 2) - P.β * ((u - u ^ 2 / 2) - (l - l ^ 2 / 2))) /
        (u - l) ∧
    0 < (u - u ^ 2 / 2) - (l - l ^ 2 / 2) := by sorry

end Teletriage.OneShot
