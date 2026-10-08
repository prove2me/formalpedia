-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_eq28_29_reservation_price
-- name    : SuReturns.PartialRefunds.eq28_29_reservation_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:01.139001+00:00
-- url     : https://prove2.me/theorems/fcb13981-9691-4cd5-b660-0148efffed90
-- title:
--   Proof of Proposition 2, (28)→(29), p. 26 — E max(V, r) = rG(r) + ∫_r^∞ v dG(v)
-- statement:
--   Let $V$ be a real random variable with law $\nu$ and finite mean, and let $G(r) = \mathbb P(V < r)$. For every real $r$,
--   $$E\max(V, r) = r\,G(r) + \int_{[r,\infty)} v\,d\nu(v).$$
--
--   This is the identity behind the step from (28) to (29) in the proof of Proposition 2: the consumer's reservation price under refund $r$ splits into the refund collected by consumers who return ($V < r$) and the valuation enjoyed by those who keep ($V \ge r$).
--
--   **Formalization Note** The page writes $\int_r^\infty v g(v)\,dv$ for a density $g$; here $\nu$ is a general law and the integral is over the closed half-line $[r,\infty)$, matching the tie rule keep iff $V \ge r$. Integrability of $V$ is the page's finite $\mu = EV$.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Proposition 2, (28)–(29)

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem eq28_29_reservation_price (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (r : ℝ) :
    reservationPrice ν r = r * returnProb ν r + ∫ v in Set.Ici r, v ∂ν := by sorry

end SuReturns.PartialRefunds
