-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_capacity_additivity_gaussian_achievability
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.capacity_additivity_gaussian_achievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:57:32.4264+00:00
-- url     : https://prove2.me/theorems/c3480f67-8ce1-4eaa-9d02-840fb0f865b8
-- title:
--   Classical capacity, Holevo additivity, and Gaussian attainment
-- statement:
--   Let $\Phi$ be any physical phase-insensitive single-mode Gaussian channel with finite parameters, and let $E\ge0$ be its finite per-use input photon budget. Let $C_\chi^{(m)}(\Phi;E)$ optimize Holevo information over all block ensembles whose average total input energy is at most $mE$, allowing entanglement across the $m$ uses. Let $C(\Phi;E)$ be the regularized per-use value, and let $\theta_E$ be the thermal state of mean photon number $E$. Then
--
--   $$C(\Phi;E)=C_\chi^{(1)}(\Phi;E)=S(\Phi(\theta_E))-S(\Phi(|0\rangle\langle0|)),$$
--   $$C_\chi^{(m)}(\Phi;E)=mC_\chi^{(1)}(\Phi;E)\quad(m\ge1).$$
--
--   The single-use optimum is attained by coherent states distributed according to $e^{-|z|^2/E}d^2z/(\pi E)$ for $E>0$, and by the vacuum Dirac law for $E=0$. The two output entropies in the difference are finite. Entropies and capacities are in bits. The optimization is unrestricted; Gaussianity describes an attaining encoding.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 6, Eqs. (22)-(23), attainment paragraph; PDF p.2

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

/-- PDF pp.2,6, (22)-(23): regularized capacity, Holevo additivity at total
block budget mE, and attainment by the exact Gaussian coherent ensemble. -/
theorem capacity_additivity_gaussian_achievability
    (Phi : Operation ℕ ℕ) (tau y E : ℝ) (hPhi : PhaseInsensitive Phi tau y)
    (hE : 0 ≤ E) :
    regularizedClassicalBits Phi E = constrainedHolevoBits id Phi E ∧
    entropyBits (Phi (thermalKernel E)) < ⊤ ∧ entropyBits (Phi vacuumOne) < ⊤ ∧
    regularizedClassicalBits Phi E = ENNReal.ofReal
      ((entropyBits (Phi (thermalKernel E))).toReal - (entropyBits (Phi vacuumOne)).toReal) ∧
    (∀ m : ℕ, 0 < m →
      constrainedHolevoBits totalPhotons (traceClassTensorPower Phi m) (m * E) =
        (m : ℝ≥0∞) * constrainedHolevoBits id Phi E) ∧
    (∃ mu : Ens.GeneralizedEnsemble ℕ, CoherentEncoding E mu ∧ AttainsCapacity Phi E mu) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
