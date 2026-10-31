-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_event_kl_comparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.event_kl_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:46:44.212773+00:00
-- url     : https://prove2.me/theorems/758508fb-e651-4394-94c2-d2c09720df33
-- title:
--   Corollary 4: For every measurable event F, P(F)<=gamma Q(F)+c_gamma D(P||Q)
-- statement:
--   Let $P\ll Q$, $\gamma>1$, and let $F$ be a measurable event. With the universal coefficient $c_\gamma$ of (434),
--
--   $$P(F)\le\gamma Q(F)+c_\gamma D(P\|Q).$$
--
--   The event bound holds on arbitrary measurable alphabets, including infinite KL.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 64, Corollary 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 4: For every measurable event F, P(F)<=gamma Q(F)+c_gamma D(P||Q). Sason--Verdu, arXiv:1508.00335v7, PDF p.64.  -/
theorem event_kl_comparison
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (g : ℝ) (hg : 1 < g) (F : Set A) (hF : MeasurableSet F) :
    P F ≤ ENNReal.ofReal g * Q F + ENNReal.ofReal (hockeyKLConstant b g) * kl b P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
