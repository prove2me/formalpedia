-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_jensen_entropy_gap
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.jensen_entropy_gap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:34:33.625184+00:00
-- url     : https://prove2.me/theorems/1409681c-7b8c-4cbe-be9a-54739e2568ce
-- title:
--   Theorem 14: beta2 D(Q||P)<=log(1+chi2(P||Q))-D(P||Q)<=beta1^{-1}D(Q||P)
-- statement:
--   For mutually absolutely continuous probability measures with $0<\beta_1,\beta_2<1$,
--
--   $$\beta_2D(Q\|P)\le\log_b(1+\chi^2(P\|Q))-D(P\|Q)
--   \le\beta_1^{-1}D(Q\|P).$$
--
--   All three divergences are finite under these positive density bounds, so the difference is an ordinary real difference. This result is independent of the unresolved infinite-moment cases of Theorem 13.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 34, Theorem 14

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 14: beta2 D(Q||P)<=log(1+chi2(P||Q))-D(P||Q)<=beta1^{-1}D(Q||P). Sason--Verdu, arXiv:1508.00335v7, PDF p.34.  -/
theorem jensen_entropy_gap
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P)
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : 0 < inverseUpperDensity Q P ∧ inverseUpperDensity Q P < 1) :
    inverseUpperDensity Q P * (kl b Q P).toReal ≤ logB b (1 + (chiSquareDiv P Q).toReal) - (kl b P Q).toReal ∧
    logB b (1 + (chiSquareDiv P Q).toReal) - (kl b P Q).toReal ≤ (inverseUpperDensity P Q)⁻¹ * (kl b Q P).toReal := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
