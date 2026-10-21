-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_noisyChannelLaw
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.noisyChannelLaw
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:37:23.314238+00:00
-- url     : https://prove2.me/theorems/82e9e582-b5ce-4445-8b28-95b65fbac9f1
-- title:
--   V.A, Eq.(5.47): noisy one-mode channel law
-- statement:
--   For fixed $k,N_c\ge0$, form the full Fock-space vacuum attenuator or amplifier with amplitude factor $k$, then apply independent circular Gaussian displacements of variance $N_c$. The resulting map $T$ is CPTP on all trace-class operators. For $\hbar>0$ and every trace-class input $X$,
--
--   $$\operatorname{Tr}(T(X)V(z))=\operatorname{Tr}(XV(kz))\exp\!\left[-\frac{\hbar}{2}\left(\frac{|k^2-1|}{2}+N_c\right)|z|^2\right].$$
--
--   The defining Fock coefficient sums converge and the Gaussian coefficient integrals are integrable. At $N_c=0$ the noise measure is Dirac zero. This includes the replacer $k=0$ and the additive-noise or identity case $k=1$.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 9, V.A, Eq.(5.47): noisy one-mode channel law

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- V.A, (5.47), p.9: actual CPTP attenuator/amplifier with independent
Gaussian noise. Includes k=0 and k=1; the modulus is |k^2-1|. -/
theorem noisyChannelLaw (k Nc : ℝ) (hk : 0 ≤ k) (hNc : 0 ≤ Nc)
    (hbar : ℝ) (hhbar : 0 < hbar) :
    IsProbabilityMeasure (gaussianDisplacementLaw Nc) ∧ IsTraceClassChannel (noisyChannel k Nc) ∧
    (∀ X, IsTraceClass X → ∀ i j,
      HasSum (fun ell => vacuumChannelTerm k ell X i j) (vacuumChannel k X i j) ∧
      Integrable (fun z => conjugateKernel (displacementMatrix z) (vacuumChannel k X) i j)
        (gaussianDisplacementLaw Nc)) ∧
    ∀ X, IsTraceClass X → ∀ z : ℂ,
      oneModeCharacteristic hbar (noisyChannel k Nc X) z =
        oneModeCharacteristic hbar X ((k : ℂ) * z) *
          Complex.exp (((-hbar / 2 * (|k ^ 2 - 1| / 2 + Nc) * Complex.normSq z : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
