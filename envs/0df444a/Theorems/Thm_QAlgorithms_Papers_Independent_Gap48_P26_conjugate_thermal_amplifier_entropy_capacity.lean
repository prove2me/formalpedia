-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_conjugate_thermal_amplifier_entropy_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.conjugate_thermal_amplifier_entropy_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:00:41.027373+00:00
-- url     : https://prove2.me/theorems/79323684-f706-4679-8971-6ee5d6d76961
-- title:
--   Conjugate thermal amplifier minimum entropy and capacity
-- statement:
--   For the thermal phase-conjugating amplifier $\widetilde{\mathcal A}_\kappa^N$, take finite $\kappa\ge1$, $N\ge0$, $E\ge0$. Its characteristic action is $\chi(z)\mapsto\chi(-\sqrt{\kappa-1}\bar z)e^{-\kappa(N+1/2)|z|^2}$. Let $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$, continuously extended by $g(0)=0$. Then
--
--   $$s_1(\widetilde{\mathcal A}_\kappa^N)=g(\kappa(N+1)-1),$$
--   $$C(\widetilde{\mathcal A}_\kappa^N;E)=g(\kappa N+(\kappa-1)(E+1))-g(\kappa(N+1)-1).$$
--
--   The minimum and capacity retain unrestricted finite-energy pure inputs and arbitrary average-energy-constrained block ensembles, respectively. At $\kappa=1$ the channel is an input-independent thermal replacer and capacity is zero.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Eqs. (30)-(31)

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

/-- PDF pp.6-7, (30)-(31): phase-conjugating thermal amplifier, including kappa=1. -/
theorem conjugate_thermal_amplifier_entropy_capacity
    (Phi : Operation ℕ ℕ) (kappa N E : ℝ)
    (hk : 1 ≤ kappa) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hPhi : PhaseInsensitive Phi (1 - kappa) (kappa * (2 * N + 1))) :
    minimumFiniteEnergy id Phi = ENNReal.ofReal (thermalEntropyBits (kappa * (N + 1) - 1)) ∧
    regularizedClassicalBits Phi E = ENNReal.ofReal
      (thermalEntropyBits (kappa * N + (kappa - 1) * (E + 1)) - thermalEntropyBits (kappa * (N + 1) - 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
