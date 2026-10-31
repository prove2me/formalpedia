-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_upper_information
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_upper_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:35:49.909752+00:00
-- url     : https://prove2.me/theorems/603df761-b99b-4d5e-bdfc-89855919543b
-- title:
--   Theorem 17: TV log e<=D+E_P|relative information|
-- statement:
--   For any probability pair $P\ll Q$, with $I=\log_b(dP/dQ)$,
--
--   $$|P-Q|\log_b e\le D(P\|Q)+E_P|I|.$$
--
--   The expectation and entropy may be infinite. The statement uses their extended nonnegative values.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 37, Theorem 17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 17: TV log e<=D+E_P|relative information|. Sason--Verdu, arXiv:1508.00335v7, PDF p.37.  -/
theorem tv_upper_information
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    fullVariation P Q * ENNReal.ofReal (logBaseE b) ≤ kl b P Q + absInfo b P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
