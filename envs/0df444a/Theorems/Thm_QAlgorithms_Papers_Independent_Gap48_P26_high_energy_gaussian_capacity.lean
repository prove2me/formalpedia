-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_high_energy_gaussian_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.high_energy_gaussian_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:02:12.0514+00:00
-- url     : https://prove2.me/theorems/ea20c437-48dc-47ba-ab85-3c3e9637e253
-- title:
--   Gaussian capacity attainment above a channel-dependent energy threshold
-- statement:
--   Fix a physical finite-parameter phase-insensitive single-mode channel $\Phi$ and fixed Gaussian input and output unitaries $V,U$, and put $\Psi=\mathcal U\circ\Phi\circ\mathcal V$. There exists a finite threshold $E_0\ge0$, depending on this fixed channel, such that for every finite $E\ge E_0$,
--
--   $$C(\Psi;E)=C_\chi^{(1)}(\Psi;E),\qquad C_\chi^{(m)}(\Psi;E)=mC_\chi^{(1)}(\Psi;E)\quad(m\ge1).$$
--
--   A Gaussian displacement law of a common pure Gaussian seed attains the single-use optimum under the ensemble-average photon constraint. The capacity optimization itself permits arbitrary block states. The threshold is not claimed uniform over the squeezing transformations.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, High-energy paragraph; PDF p.4

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

/-- PDF pp.4,7: a finite threshold depending on this fixed normal-form channel.
No uniform bound over squeezing parameters or all-energy assertion is made. -/
theorem high_energy_gaussian_capacity
    (Phi : Operation ℕ ℕ) (tau y : ℝ) (hPhi : PhaseInsensitive Phi tau y)
    (U V : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ)
    (hU : AffineGaussianUnitary U) (hV : AffineGaussianUnitary V) :
    ∃ Ezero : ℝ, 0 ≤ Ezero ∧ ∀ E : ℝ, Ezero ≤ E →
      let Psi := normalFormChannel Phi U V
      regularizedClassicalBits Psi E = constrainedHolevoBits id Psi E ∧
      (∀ m : ℕ, 0 < m →
        constrainedHolevoBits totalPhotons (traceClassTensorPower Psi m) (m * E) =
          (m : ℝ≥0∞) * constrainedHolevoBits id Psi E) ∧
      ∃ mu : Ens.GeneralizedEnsemble ℕ, GaussianEncoding mu ∧ AttainsCapacity Psi E mu := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
