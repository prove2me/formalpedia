-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_relative_entropy_ratio
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.relative_entropy_ratio
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:31:39.818547+00:00
-- url     : https://prove2.me/theorems/8baa4077-d3f1-441a-be72-d646febd6881
-- title:
--   Theorem 7: kappa(beta2)<=D(P||Q)/D(Q||P)<=kappa(beta1^{-1}), kappa=r(t)/[(t-1)log e-log t]
-- statement:
--   For distinct mutually absolutely continuous probability measures with $0<\beta_1,\beta_2<1$, put $\kappa(t)=r(t)/[(t-1)\log_b e-\log_b t]$. Then
--
--   $$\kappa(\beta_2)D(Q\|P)\le D(P\|Q)\le\kappa(\beta_1^{-1})D(Q\|P).$$
--
--   The positive essential bounds ensure that both entropies are finite and positive, so this is exactly the displayed quotient bound (173).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 25, Theorem 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 7: kappa(beta2)<=D(P||Q)/D(Q||P)<=kappa(beta1^{-1}), kappa=r(t)/[(t-1)log e-log t]. Sason--Verdu, arXiv:1508.00335v7, PDF p.25.  -/
theorem relative_entropy_ratio
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) (hne : P ≠ Q)
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : 0 < inverseUpperDensity Q P ∧ inverseUpperDensity Q P < 1) :
    ENNReal.ofReal (entropyKernel b (inverseUpperDensity Q P)) * kl b Q P ≤ kl b P Q ∧
    kl b P Q ≤ ENNReal.ofReal (entropyKernel b (inverseUpperDensity P Q)⁻¹) * kl b Q P := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
