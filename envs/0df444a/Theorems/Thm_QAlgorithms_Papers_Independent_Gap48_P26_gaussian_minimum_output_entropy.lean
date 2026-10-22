-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_gaussian_minimum_output_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.gaussian_minimum_output_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:53:02.896266+00:00
-- url     : https://prove2.me/theorems/80902c17-1137-4633-afd5-cbd9ae619d79
-- title:
--   Finite-energy Gaussian minimum output entropy
-- statement:
--   Let $\Phi$ be a single-mode phase-covariant or phase-contravariant Gaussian channel on the full bosonic Fock space. Its Weyl characteristic action is $\chi_\rho(z)\mapsto\chi_\rho(\sqrt\tau z)e^{-y|z|^2/2}$ for $\tau\ge0$, and $\chi_\rho(z)\mapsto\chi_\rho(-\sqrt{|\tau|}\bar z)e^{-y|z|^2/2}$ for $\tau<0$, with finite real parameters $y\ge|\tau-1|$. Let $m\ge1$. Write $S$ for von Neumann entropy in bits and $s_m$ for the infimum of the output entropy over all normalized pure $m$-mode inputs of finite expected total photon number. There is no common energy ceiling in this infimum. Then
--
--   $$s_m=m s_1=mS(\Phi(|0\rangle\langle0|))=S(\Phi^{\otimes m}(|0\rangle\langle0|^{\otimes m})).$$
--
--   Thus the product vacuum attains the minimum, including against entangled inputs.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 2, Eq. (2)

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

/-- PDF pp.2-4, (2): tensor powers of one phase-insensitive single-mode channel.
All pure finite-energy inputs are included; the vacuum attains the infimum. -/
theorem gaussian_minimum_output_entropy
    (Phi : Operation ℕ ℕ) (tau y : ℝ) (hPhi : PhaseInsensitive Phi tau y)
    (m : ℕ) (hm : 0 < m) :
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Phi m) =
      (m : ℝ≥0∞) * minimumFiniteEnergy id Phi ∧
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Phi m) =
      (m : ℝ≥0∞) * entropyBits (Phi vacuumOne) ∧
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Phi m) =
      entropyBits (traceClassTensorPower Phi m (vacuum m)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
