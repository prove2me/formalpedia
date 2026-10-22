-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_amplifier_vacuum_minimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.amplifier_vacuum_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:53:53.62825+00:00
-- url     : https://prove2.me/theorems/51116aa7-43db-422e-b1bd-bd629c39c32e
-- title:
--   Quantum-limited amplifier vacuum minimum
-- statement:
--   Let $\mathcal A_\kappa$ be the single-mode quantum-limited amplifier of finite intensity gain $\kappa\ge1$, with characteristic action $\chi(z)\mapsto\chi(\sqrt\kappa z)e^{-(\kappa-1)|z|^2/2}$. For every unit Fock vector $\psi$ with finite mean photon number,
--
--   $$S(\mathcal A_\kappa(|\psi\rangle\langle\psi|))\ge S(\mathcal A_\kappa(|0\rangle\langle0|)),\qquad s_1(\mathcal A_\kappa)=S(\mathcal A_\kappa(|0\rangle\langle0|)).$$
--
--   Entropy is measured in bits. The identity endpoint $\kappa=1$ is included. This is the one-mode minimum used in the channel result.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 4, Eqs. (4), (12)

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

/-- PDF pp.3-4, (4),(12): quantum-limited amplifier, including gain one. -/
theorem amplifier_vacuum_minimum
    (A : Operation ℕ ℕ) (kappa : ℝ) (hk : 1 ≤ kappa)
    (hA : PhaseInsensitive A kappa (kappa - 1))
    (u : Hilbert ℕ) (hu : ‖u‖ = 1) (he : weightedPhotonExpectation id (rankOne u) < ⊤) :
    entropyBits (A vacuumOne) ≤ entropyBits (A (rankOne u)) ∧
    minimumFiniteEnergy id A = entropyBits (A vacuumOne) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
