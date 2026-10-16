-- Prove2me | Theorems.Thm_PersPricingDist_PersonalA_contributions
-- name    : PersPricingDist.PersonalA.contributions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:02.706272+00:00
-- url     : https://prove2.me/theorems/c1816f58-81d0-4ea4-bc41-6a20883e25e5
-- title:
--   OA p. 7 — closed forms of A's and B's contributions
-- statement:
--   For $0<s<v<1$ and $X\ge v/s$, let $\alpha$ integrate A's valuation advantage over $[0,\hat x]$ and $\beta$ integrate B's advantage over $[\hat x,X]$. Then
--   $$\alpha=\frac{(1-v)^2}{2(1-s)},\qquad \beta=\frac{(v-s)^2}{2s(1-s)}.$$
--
--   These formulas translate the valuation parameters into the channel contributions used in Proposition 4. In particular, extending $X$ beyond $v/s$ does not change either contribution.
-- source:
--   Jullien, Reisinger & Rey, authors' manuscript of March 2022 (doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), p. 6 (PDF 8); OA p. 7 (PDF 40)

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

namespace PersPricingDist.PersonalA

theorem contributions (M : Model) (hM : M.Standing) :
    M.alpha = (1 - M.v) ^ 2 / (2 * (1 - M.s)) ∧
    M.beta = (M.v - M.s) ^ 2 / (2 * M.s * (1 - M.s)) := by sorry

end PersPricingDist.PersonalA
