-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_two_sided_thresholds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_two_sided_thresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:37:55.882709+00:00
-- url     : https://prove2.me/theorems/cd8a7c68-24eb-484c-8f98-eaa41a9b681a
-- title:
--   Theorem 21: TV>=(1-exp(-eta1))P_P(i>=eta1)+(exp(eta2)-1)P_P(i<=-eta2), with equality for the binary laws (283),(284)
-- statement:
--   For mutually absolutely continuous probability measures and any $\eta_1,\eta_2>0$,
--
--   $$|P-Q|\ge(1-\exp_b(-\eta_1))P[I\ge\eta_1]
--    +(\exp_b(\eta_2)-1)P[I\le-\eta_2].$$
--
--   Equality holds for the binary laws with $P(0)=(1-\exp_b(-\eta_2))/(1-\exp_b(-\eta_1-\eta_2))$ and $Q(0)=\exp_b(-\eta_1)P(0)$. Positive thresholds ensure that the denominator is nonzero. Both the inequality and the explicit attaining laws are included.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 40, Theorem 21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 21: TV>=(1-exp(-eta1))P_P(i>=eta1)+(exp(eta2)-1)P_P(i<=-eta2), with equality for the binary laws (283),(284). Sason--Verdu, arXiv:1508.00335v7, PDF p.40.  -/
theorem tv_two_sided_thresholds
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P)
    (e1 e2 : ℝ) (h1 : 0 < e1) (h2 : 0 < e2) :
    ENNReal.ofReal (1 - expB b (-e1)) * P {x | (e1 : EReal) ≤ relativeInfo b P Q x} +
      ENNReal.ofReal (expB b e2 - 1) * P {x | relativeInfo b P Q x ≤ (-e2 : EReal)} ≤ fullVariation P Q ∧
    (let p := (1 - expB b (-e2)) / (1 - expB b (-e1 - e2))
     let P0 := binary p
     let Q0 := binary (expB b (-e1) * p)
     IsProbabilityMeasure P0 ∧ IsProbabilityMeasure Q0 ∧ P0 ≪ Q0 ∧ Q0 ≪ P0 ∧
       fullVariation P0 Q0 = ENNReal.ofReal (1 - expB b (-e1)) * P0 {x | (e1 : EReal) ≤ relativeInfo b P0 Q0 x} +
         ENNReal.ofReal (expB b e2 - 1) * P0 {x | relativeInfo b P0 Q0 x ≤ (-e2 : EReal)}) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
