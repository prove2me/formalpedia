-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_conjugate_amplifier_measure_prepare
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.conjugate_amplifier_measure_prepare
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:54:44.983978+00:00
-- url     : https://prove2.me/theorems/7fc5cb65-d3c0-473c-9374-7011668e8f36
-- title:
--   Conjugate amplifier coherent measure-and-prepare representation
-- statement:
--   Let $\widetilde{\mathcal A}_\kappa$ be the quantum-limited conjugate amplifier, $\kappa\ge1$, defined on every Fock density operator by $\chi(z)\mapsto\chi(-\sqrt{\kappa-1}\bar z)e^{-\kappa|z|^2/2}$. For every density operator $\rho$,
--
--   $$\widetilde{\mathcal A}_\kappa(\rho)=\int_{\mathbb C}\frac{d^2z}{\pi}\,\langle z|\rho|z\rangle\,|\sqrt{\kappa-1}\bar z\rangle\langle\sqrt{\kappa-1}\bar z|.$$
--
--   Here $|z\rangle=D(z)|0\rangle$. Every displayed matrix-coefficient integral is integrable. This gives an exact channel representation on arbitrary inputs.
--
--   **Source correction.** The printed preparation amplitude is $-\sqrt\kappa\bar z$. Both its magnitude and sign are corrected to agree with Eq. (14); independent moderation is pending.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 3, Eq. (5), corrected using Eq. (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)

open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,6, (5),(14): corrected coherent measure-and-prepare identity.
Printed |-sqrt(kappa) conjugate(z)>; changed to |+sqrt(kappa-1) conjugate(z)>.
Both changes are forced by (14), including the vacuum endpoint and Weyl phase. -/
theorem conjugate_amplifier_measure_prepare
    (C : Operation ℕ ℕ) (kappa : ℝ) (hk : 1 ≤ kappa)
    (hC : PhaseInsensitive C (1 - kappa) kappa) (rho : State ℕ) :
    ∀ a b : ℕ,
      Integrable (fun z : ℂ =>
        (B.husimiQ (B.operatorOfMatrix rho.coefficients) z : ℂ) *
          coherentKernel ((Real.sqrt (kappa - 1) : ℂ) * star z) a b) B.coherentMeasure ∧
      C rho.coefficients a b = ∫ z : ℂ,
        (B.husimiQ (B.operatorOfMatrix rho.coefficients) z : ℂ) *
          coherentKernel ((Real.sqrt (kappa - 1) : ℂ) * star z) a b ∂B.coherentMeasure := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
