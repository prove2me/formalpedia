-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_finite_iteration_entropy_estimate
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.finite_iteration_entropy_estimate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:56:52.62999+00:00
-- url     : https://prove2.me/theorems/ffe19889-7fc9-4bb3-b354-f867674d3090
-- title:
--   Finite-iteration amplifier entropy estimate
-- statement:
--   Let $\kappa\ge1$ be finite, $\eta=(\kappa-1)/\kappa$, and let $\mathcal A_\kappa$ and $\mathcal E_\eta$ be the quantum-limited amplifier and attenuator. For every unit finite-energy Fock vector $\psi$ and integer $q\ge0$, put $\sigma_q=\mathcal E_\eta^q(|\psi\rangle\langle\psi|)$. All three entropies below are finite, and
--
--   $$S(\mathcal A_\kappa(|\psi\rangle\langle\psi|))\ge S(\mathcal A_\kappa(\sigma_q))-S(\sigma_q).$$
--
--   Entropy is in bits. This is the finite-iteration estimate itself; the relative-entropy proof step (10) is not a hypothesis.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 4, Eq. (11)

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

/-- PDF p.4, (11): finite-iteration estimate, with finite real entropies and the
source's subtraction order. No relative-entropy premise is added. -/
theorem finite_iteration_entropy_estimate
    (A L : Operation ℕ ℕ) (kappa : ℝ) (hk : 1 ≤ kappa)
    (hA : PhaseInsensitive A kappa (kappa - 1))
    (hL : PhaseInsensitive L ((kappa - 1) / kappa) (1 - (kappa - 1) / kappa))
    (u : Hilbert ℕ) (hu : ‖u‖ = 1) (he : weightedPhotonExpectation id (rankOne u) < ⊤)
    (q : ℕ) :
    let X := (L^[q]) (rankOne u)
    entropyBits (A (rankOne u)) < ⊤ ∧ entropyBits (A X) < ⊤ ∧ entropyBits X < ⊤ ∧
    (entropyBits (A (rankOne u))).toReal ≥
      (entropyBits (A X)).toReal - (entropyBits X).toReal := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
