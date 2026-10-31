-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_upper_thresholds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_upper_thresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:36:09.554993+00:00
-- url     : https://prove2.me/theorems/8182500c-7acc-48cb-ad5d-9a0a798f6109
-- title:
--   Theorem 18: For beta0 in [beta1,1], TV/2<=(1-beta0)P_P(i>0)+(beta0-beta1)P_P(i>log(1/beta0)); the analogous Q-law bound (268) holds for beta0 in [beta2,1]
-- statement:
--   Let $P\ll Q$ with $\beta_1,\beta_2<1$ and put $I=\log_b(dP/dQ)$. For every $t\in[\beta_1,1]$,
--
--   $$\frac{|P-Q|}{2}\le(1-t)P[I>0]+(t-\beta_1)P[I>\log_b(1/t)].$$
--
--   For every $t\in[\beta_2,1]$, the corresponding bound is $(1-t)Q[I<0]+(t-\beta_2)Q[I<\log_b t]$. Both admit equality for suitable distinct binary laws, with thresholds $t=\beta_1$ and $t=\beta_2$, respectively. Extended logarithms handle $t=0$; all events retain strict inequalities.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 37, Theorem 18

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 18: For beta0 in [beta1,1], TV/2<=(1-beta0)P_P(i>0)+(beta0-beta1)P_P(i>log(1/beta0)); the analogous Q-law bound (268) holds for beta0 in [beta2,1]. Sason--Verdu, arXiv:1508.00335v7, PDF p.37.  -/
theorem tv_upper_thresholds
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (hb1 : inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    (∀ t : ℝ, inverseUpperDensity P Q ≤ t → t ≤ 1 →
      fullVariation P Q / 2 ≤ ENNReal.ofReal (1 - t) * P {x | 0 < relativeInfo b P Q x} +
        ENNReal.ofReal (t - inverseUpperDensity P Q) * P {x | elogB b ((ENNReal.ofReal t)⁻¹) < relativeInfo b P Q x}) ∧
    (∀ t : ℝ, inverseUpperDensity Q P ≤ t → t ≤ 1 →
      fullVariation P Q / 2 ≤ ENNReal.ofReal (1 - t) * Q {x | relativeInfo b P Q x < 0} +
        ENNReal.ofReal (t - inverseUpperDensity Q P) * Q {x | relativeInfo b P Q x < elogB b (ENNReal.ofReal t)}) ∧
    (∃ P0 Q0 : Measure Bool, IsProbabilityMeasure P0 ∧ IsProbabilityMeasure Q0 ∧
      P0 ≪ Q0 ∧ P0 ≠ Q0 ∧ inverseUpperDensity P0 Q0 < 1 ∧ inverseUpperDensity Q0 P0 < 1 ∧
      fullVariation P0 Q0 / 2 = ENNReal.ofReal (1 - inverseUpperDensity P0 Q0) * P0 {x | 0 < relativeInfo b P0 Q0 x} ∧
      fullVariation P0 Q0 / 2 = ENNReal.ofReal (1 - inverseUpperDensity Q0 P0) * Q0 {x | relativeInfo b P0 Q0 x < 0}) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
