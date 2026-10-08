-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_eq27_30_margin_identity
-- name    : SuReturns.PartialRefunds.eq27_30_margin_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:11.816756+00:00
-- url     : https://prove2.me/theorems/491c4677-ddb2-4eb7-8b0a-fc73a53eebc1
-- title:
--   Proof of Proposition 2, (27)–(30), p. 26 — at p = E max(V, r) the margin is ∫_r^∞ (v − s) dG(v)
-- statement:
--   Let $V$ have law $\nu$ with finite mean, $\bar G(r) = \mathbb P(V \ge r)$ and $G(r) = \mathbb P(V < r)$. For all real $s$ and $r$, at the price $p = E\max(V, r)$,
--   $$(p - s)\bar G(r) + (p - r)G(r) = \int_{[r,\infty)} (v - s)\,d\nu(v).$$
--
--   This is the chain (27)–(30) of the proof of Proposition 2: when the seller charges the highest price consumers accept, the expected margin per unit sold (the bracket of (8)) depends on the refund $r$ only through the surplus over salvage value of the consumers who keep the product.
--
--   **Formalization Note** $\int_r^\infty (v-s) g(v)\,dv$ is written for a general law $\nu$ as an integral over $[r,\infty)$.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Proposition 2, (27)–(30)

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem eq27_30_margin_identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s r : ℝ) :
    margin ν s (reservationPrice ν r) r = ∫ v in Set.Ici r, (v - s) ∂ν := by sorry

end SuReturns.PartialRefunds
