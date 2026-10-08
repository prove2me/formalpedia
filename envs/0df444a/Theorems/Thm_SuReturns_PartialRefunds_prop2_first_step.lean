-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_prop2_first_step
-- name    : SuReturns.PartialRefunds.prop2_first_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:09.317889+00:00
-- url     : https://prove2.me/theorems/36d66e0a-2081-4db1-8fcf-3467ca93ce8b
-- title:
--   Proof of Proposition 2, first step, p. 26 — (E max(V, s), s) maximizes the margin subject to p ≤ E max(V, r)
-- statement:
--   Let $V$ have law $\nu$ with finite mean, $\bar G(r) = \mathbb P(V \ge r)$, $G(r) = \mathbb P(V < r)$, and let $s$ be real. Write $m(p, r) = (p - s)\bar G(r) + (p - r)G(r)$ for the bracket of (8). For every price $p$ and refund $r$ with $p \le E\max(V, r)$,
--   $$m(p, r) \;\le\; m\big(E\max(V, s),\, s\big).$$
--
--   This is the first step of the proof of Proposition 2: among all price–refund pairs at which consumers are willing to buy, the expected margin per unit sold is largest at $p^* = E\max(V, s)$, $r^* = s$. Together with the newsvendor step it yields Proposition 2.
--
--   **Formalization Note** The constraint $p \le E\max(V, r)$ is the page's "so that consumers are willing to buy in the first place" (demand rule (6)). Only optimality is claimed, not uniqueness.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Proposition 2, first paragraph and (27)–(30)

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem prop2_first_step (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s : ℝ) :
    ∀ p r, p ≤ reservationPrice ν r → margin ν s p r ≤ margin ν s (reservationPrice ν s) s := by sorry

end SuReturns.PartialRefunds
