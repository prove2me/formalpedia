-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_thermal_attenuator_entropy_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.thermal_attenuator_entropy_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:58:09.588697+00:00
-- url     : https://prove2.me/theorems/cff78c6a-f67f-4a4a-b44e-69733b622520
-- title:
--   Thermal attenuator minimum entropy and capacity
-- statement:
--   For a thermal attenuator $\mathcal E_\eta^N$ on full Fock states, let $0\le\eta\le1$, $N\ge0$, and $E\ge0$ be finite. Its characteristic action is $\chi(z)\mapsto\chi(\sqrt\eta z)e^{-(1-\eta)(N+1/2)|z|^2}$. With $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ and $g(0)=0$,
--
--   $$s_1(\mathcal E_\eta^N)=g((1-\eta)N),\qquad C(\mathcal E_\eta^N;E)=g(\eta E+(1-\eta)N)-g((1-\eta)N).$$
--
--   Here $s_1$ minimizes over all finite-mean-energy pure inputs and $C$ is the unrestricted regularized classical capacity under the average photon budget. Both endpoints and zero noise and energy are included.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Eqs. (24)-(25)

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

/-- PDF pp.6-7, (24)-(25): thermal attenuation, including eta=0,1 and N=E=0. -/
theorem thermal_attenuator_entropy_capacity
    (Phi : Operation ℕ ℕ) (eta N E : ℝ)
    (heta : eta ∈ Set.Icc 0 1) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hPhi : PhaseInsensitive Phi eta ((1 - eta) * (2 * N + 1))) :
    minimumFiniteEnergy id Phi = ENNReal.ofReal (thermalEntropyBits ((1 - eta) * N)) ∧
    regularizedClassicalBits Phi E = ENNReal.ofReal
      (thermalEntropyBits (eta * E + (1 - eta) * N) - thermalEntropyBits ((1 - eta) * N)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
