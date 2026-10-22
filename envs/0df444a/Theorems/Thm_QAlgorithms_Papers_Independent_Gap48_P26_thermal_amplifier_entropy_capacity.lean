-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_thermal_amplifier_entropy_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.thermal_amplifier_entropy_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:59:42.898429+00:00
-- url     : https://prove2.me/theorems/d83fcb21-9cce-436f-beaf-c24a7175eab3
-- title:
--   Thermal amplifier minimum entropy and capacity
-- statement:
--   For a thermal amplifier $\mathcal A_\kappa^N$, let finite $\kappa\ge1$, $N\ge0$, and $E\ge0$ denote intensity gain, environmental mean photon number and per-use average input budget. Its characteristic action is $\chi(z)\mapsto\chi(\sqrt\kappa z)e^{-(\kappa-1)(N+1/2)|z|^2}$. With thermal entropy $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ and $g(0)=0$,
--
--   $$s_1(\mathcal A_\kappa^N)=g((\kappa-1)(N+1)),$$
--   $$C(\mathcal A_\kappa^N;E)=g(\kappa E+(\kappa-1)(N+1))-g((\kappa-1)(N+1)).$$
--
--   Inputs range over full Fock states; the entropy minimum is over finite-energy pure inputs and capacity is optimized over arbitrary block ensembles. The gain-one identity endpoint is included.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Eqs. (28)-(29)

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

/-- PDF pp.6-7, (28)-(29): thermal amplification, including kappa=1. -/
theorem thermal_amplifier_entropy_capacity
    (Phi : Operation ℕ ℕ) (kappa N E : ℝ)
    (hk : 1 ≤ kappa) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hPhi : PhaseInsensitive Phi kappa ((kappa - 1) * (2 * N + 1))) :
    minimumFiniteEnergy id Phi = ENNReal.ofReal (thermalEntropyBits ((kappa - 1) * (N + 1))) ∧
    regularizedClassicalBits Phi E = ENNReal.ofReal
      (thermalEntropyBits (kappa * E + (kappa - 1) * (N + 1)) - thermalEntropyBits ((kappa - 1) * (N + 1))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
