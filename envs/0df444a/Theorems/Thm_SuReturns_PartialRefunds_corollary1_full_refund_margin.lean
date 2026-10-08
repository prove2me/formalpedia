-- Prove2me | Theorems.Thm_SuReturns_PartialRefunds_corollary1_full_refund_margin
-- name    : SuReturns.PartialRefunds.corollary1_full_refund_margin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:08.99447+00:00
-- url     : https://prove2.me/theorems/e140cfd6-e2a3-44df-9b56-1519e54ba98b
-- title:
--   Proof of Corollary 1, p. 26 — E max(V, s) − s ≥ (p − s)Ḡ(p) for every price p
-- statement:
--   Let $V$ have law $\nu$ with finite mean, $\bar G(p) = \mathbb P(V \ge p)$, and let $s$ be real. For every real $p$,
--   $$(p - s)\bar G(p) \;\le\; E\max(V, s) - s.$$
--
--   The proof of Corollary 1 applies this at the optimal full-refund price $p^*_F$: the per-unit margin under full refunds never exceeds the per-unit margin $E\max(V,s) - s$ of the optimal partial refund, which is why the optimal quantity under partial refunds is larger.
--
--   **Formalization Note** The page states the inequality at $p^*_F$ and notes $p^*_F \ge s$; it holds for every real $p$ (for $p \le s$ the left side is $\le 0 \le E\max(V,s) - s$), and is stated in that form.
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451 (version of August 2008), p. 26, proof of Corollary 1

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

namespace SuReturns.PartialRefunds

theorem corollary1_full_refund_margin (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s : ℝ) :
    ∀ p, (p - s) * keepProb ν p ≤ reservationPrice ν s - s := by sorry

end SuReturns.PartialRefunds
