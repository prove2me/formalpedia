-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_sup_over_c_one
-- name    : RobustSPA.FixedReserve.sup_over_c_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:58.482544+00:00
-- url     : https://prove2.me/theorems/e1dcf0d5-d5d8-4693-9f2f-2cda5314ef7a
-- title:
--   Proof of Proposition 5, p. App-11 — for n = 1, max over c ∈ [0, 1] of rc + (1−r)(1−c) is max(1 − r, r)
-- statement:
--   Let $r\in[0,1]$. The linear function $c\mapsto r\,c+(1-r)(1-c)$ attains on $[0,1]$ the maximum
--   $$\max_{c\in[0,1]}\big(r\,c+(1-r)(1-c)\big)=\max(1-r,\,r).$$
--
--   This is the single-buyer case of the proof of Proposition 5: with one buyer the regret of $\mathrm{SPA}(r)$ reduces to an expression linear in the mass $c$ placed below the reserve, so the worst case is at an endpoint.
--
--   **Formalization Note** The page prints the expression as "$\lambda-1+rc+(1-r)(1-c)$"; the "$\lambda-1$" is a stray term (the stated value $\max(1-r,r)$ is that of $rc+(1-r)(1-c)$), and the statement omits it.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-11, Proof of Proposition 5 (case n = 1)

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proof of Proposition 5, p. App-11 (case `n = 1`): for `r ∈ [0,1]`, the maximum of the
linear function `c ↦ r c + (1 − r)(1 − c)` over `c ∈ [0,1]` is `max(1 − r, r)`. -/
theorem sup_over_c_one (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun c : ℝ => r * c + (1 - r) * (1 - c)) '' Set.Icc 0 1) (max (1 - r) r) := by sorry

end RobustSPA.FixedReserve
