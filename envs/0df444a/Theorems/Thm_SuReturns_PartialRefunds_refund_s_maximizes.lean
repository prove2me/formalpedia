-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_refund_s_maximizes
-- name    : SuReturns.PartialRefunds.refund_s_maximizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:01.785732+00:00
-- url     : https://prove2.me/theorems/baa1da72-9239-4b82-9cb6-0b4521b2a1c3
-- title:
--   Proof of Proposition 2, after (30), p. 26 — ∫_r^∞ (v − s) dG(v) is maximized at r = s
-- statement:
--   Let $V$ have law $\nu$ with finite mean, and let $s$ be real. For every real $r$,
--   $$\int_{[r,\infty)} (v - s)\,d\nu(v) \;\le\; \int_{[s,\infty)} (v - s)\,d\nu(v).$$
--
--   This is the sentence "This is maximized when $r = s$" of the proof of Proposition 2: by (27)–(30) the seller's margin at the highest acceptable price is $\int_r^\infty (v-s)\,dG$, so the refund equal to the salvage value is optimal.
--
--   **Formalization Note** Only the optimality of $r = s$ is stated, not uniqueness: if $\nu$ puts no mass between $s$ and $r$, the refund $r$ is optimal too.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Proposition 2, sentence after (30)

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem refund_s_maximizes (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s r : ℝ) :
    ∫ v in Set.Ici r, (v - s) ∂ν ≤ ∫ v in Set.Ici s, (v - s) ∂ν := by sorry

end SuReturns.PartialRefunds
