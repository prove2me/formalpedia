-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_measurement_robustness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.measurement_robustness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:04:19.545037+00:00
-- url     : https://prove2.me/theorems/9592ddf7-58f8-4ae3-880d-5616a4452a71
-- title:
--   Lemma 8: incompatibility and channel robustness coincide
-- statement:
--   Let $\{M_{a\mid x}\}$ be finitely many POVMs with positive numbers of settings, outcomes, and quantum input dimension. A compatible family is obtained by classical conditional-probability postprocessing of a finite normalized parent POVM. Let $\mathcal O_{\rm all}$ be exactly the measurement-channel family (G2), and let $\mathcal O$ contain exactly the channels of compatible POVMs. The channel is the complex-linear matrix-unit extension of
--   $$E_M(\sigma\otimes\rho)=\sum_{x,a}\langle x|\sigma|x\rangle\operatorname{Tr}(M_{a\mid x}\rho)|a\rangle\langle a|.$$
--   Define $R_C(M)$ as the minimum of $1+r$, $r\ge0$, such that $(M+rN)/(1+r)$ is compatible for a physical POVM family $N$. Let $R_{\mathcal O}$ be generalized channel robustness with noise restricted to $\mathcal O_{\rm all}$, not to arbitrary CPTP maps. Then
--   $$R_C(M)=R_{\mathcal O}(E_M).$$
--   Both minima are attained by actual noise and compatible witnesses with the same $r$, and their channel mixture equality holds on every joint input operator.
--
--   The matrix-unit extension preserves complex linearity and agrees with the displayed product-state formula. The qualitative remark about other robustness variants and weight measures is not converted into unspecified extra results.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 15, Lemma 8: incompatibility and channel robustness coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Lemma 8, PDF pp.15-16 (G4)-(G5): channel generalized robustness with
noise RESTRICTED to the measurement-channel family equals incompatibility
robustness. Both physical minima have witnesses with the same r,N,F.
The qualitative final sentence about weight measures is not made quantitative. -/
theorem measurement_robustness (O : ResourceTheory) {x a d : ℕ+}
    (hallowed : O.allowed (measurementPort x a d) =
      {J | ∃ M : MeasurementFamily x a d, ValidMeasurements M ∧ J = measurementChoi M})
    (hfree : O.free (measurementPort x a d) =
      {J | ∃ M : MeasurementFamily x a d, CompatiblePOVMs M ∧ J = measurementChoi M})
    (M : MeasurementFamily x a d) (hM : ValidMeasurements M) :
    incompatibility M = maximal O (measurementChoi M) ∧
    IsLeast (measurementValues M) (incompatibility M) ∧
    ∃ r : ℝ, 0 ≤ r ∧ ENNReal.ofReal (1 + r) = incompatibility M ∧
      ∃ N F : MeasurementFamily x a d, ValidMeasurements N ∧ CompatiblePOVMs F ∧
        (∀ s o, M s o + (r : ℂ) • N s o = ((1 + r : ℝ) : ℂ) • F s o) ∧
        measurementChoi N ∈ O.allowed (measurementPort x a d) ∧
        measurementChoi F ∈ O.free (measurementPort x a d) ∧
        measurementChoi M + (r : ℂ) • measurementChoi N =
          ((1 + r : ℝ) : ℂ) • measurementChoi F := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
