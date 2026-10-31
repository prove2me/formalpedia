-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_lower_information
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_lower_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:38:20.952391+00:00
-- url     : https://prove2.me/theorems/15be087d-daf2-414d-871c-25957afba367
-- title:
--   Theorem 22: TV log e>=E_P|i|-D, interpreted as TV log e+D>=E_P|i| when D may be infinite
-- statement:
--   For mutually absolutely continuous probability measures, with $I=\log_b(dP/dQ)$,
--
--   $$E_P|I|\le |P-Q|\log_b e+D(P\|Q),\qquad
--   2E_P I^-\le |P-Q|\log_b e.$$
--
--   The first is the subtraction-free reading of (286); the second is the proof form (288)–(289), retaining information even when KL is infinite. The negative information moment is finite.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 40, Theorem 22

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 22: TV log e>=E_P|i|-D, interpreted as TV log e+D>=E_P|i| when D may be infinite. Sason--Verdu, arXiv:1508.00335v7, PDF p.40.  -/
theorem tv_lower_information
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    absInfo b P Q ≤ fullVariation P Q * ENNReal.ofReal (logBaseE b) + kl b P Q ∧
    2 * negativeInfo b P Q ≤ fullVariation P Q * ENNReal.ofReal (logBaseE b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
