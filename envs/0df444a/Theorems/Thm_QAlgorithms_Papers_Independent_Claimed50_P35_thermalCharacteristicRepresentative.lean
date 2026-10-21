-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_thermalCharacteristicRepresentative
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.thermalCharacteristicRepresentative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:41:21.862055+00:00
-- url     : https://prove2.me/theorems/c7c0191e-b052-461a-a1c0-6493b2f5d652
-- title:
--   V.B, Eq.(5.52): thermal characteristic representative
-- statement:
--   Let $k,N_c\ge0$, $k^2\ne1$, and $\hbar>0$. Put $\gamma=1/2+N_c/|k^2-1|$. Let $A z=z/\sqrt{|k^2-1|}$ for attenuation and $A z=\overline z/\sqrt{|k^2-1|}$ for amplification, using complex coordinates. The actual representative $\rho_\gamma$ is a normalized thermal density and
--
--   $$\operatorname{Tr}(\rho_\gamma V(z))=f(Az)=\exp\!\left[-\frac{\hbar(|k^2-1|/2+N_c)}{2|k^2-1|}|z|^2\right].$$
--
--   Here $f$ is the original channel's Weyl multiplier. The exclusion concerns this singular defect representation alone, not the existence of the channel at $k=1$.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.B, Eq.(5.52): thermal characteristic representative

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

/-- V.B, (5.52), p.10: actual thermal weylTraceCharacteristic representative, hbar
restored. k^2=1 is excluded only from this singular weylDefectPair representation. -/
theorem thermalCharacteristicRepresentative (k Nc hbar : ℝ)
    (hk : 0 ≤ k) (hNc : 0 ≤ Nc) (hhbar : 0 < hbar) (hk1 : k ^ 2 ≠ 1) :
    RealizedDensity (generalizedThermal (1 / 2 + Nc / |k ^ 2 - 1|)) ∧
    ∀ z : ℂ, oneModeCharacteristic hbar
      (generalizedThermal (1 / 2 + Nc / |k ^ 2 - 1|)) z =
        oneModeMultiplier k Nc hbar (defectRescale k z) ∧
      oneModeMultiplier k Nc hbar (defectRescale k z) = Complex.exp (((-hbar * (|k ^ 2 - 1| / 2 + Nc) /
          (2 * |k ^ 2 - 1|) * Complex.normSq z : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
