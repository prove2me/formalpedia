-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_reverse_pinsker_density
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.reverse_pinsker_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:39:36.676065+00:00
-- url     : https://prove2.me/theorems/da6883e3-8a2e-4667-937e-bb5e30f3da9f
-- title:
--   Theorem 26: bounded-density reverse Pinsker inequality (332)
-- statement:
--   If $0<\beta_1<1$ and $0\le\beta_2<1$, then
--
--   $$D(P\|Q)\le\frac{\phi(\beta_1^{-1})-\phi(\beta_2)}2|P-Q|,$$
--
--   where $\phi(0)=0$, $\phi(1)=\log_b e$, and $\phi(t)=t\log_b t/(t-1)$ otherwise. Positive $\beta_1$ implies $P\ll Q$ and finite entropy; $\beta_2$ may be zero.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 47, Theorem 26

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 26: bounded-rnDensityReal reverse Pinsker inequality (332). Sason--Verdu, arXiv:1508.00335v7, PDF p.47.  -/
theorem reverse_pinsker_density
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    kl b P Q ≤ ENNReal.ofReal ((reversePinskerPhi b (inverseUpperDensity P Q)⁻¹ - reversePinskerPhi b (inverseUpperDensity Q P)) / 2) * fullVariation P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
