-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_squeezed_thermal_entanglement_formation
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.squeezed_thermal_entanglement_formation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:03:21.390993+00:00
-- url     : https://prove2.me/theorems/9443ef31-fd11-4b1c-bfeb-c127c31f24a4
-- title:
--   Entanglement of formation of the squeezed thermal family
-- statement:
--   Let finite $\kappa\ge1$ and $N\ge0$ determine the two-mode state $\rho(\kappa,N)=U_\kappa(\theta_N\otimes|0\rangle\langle0|)U_\kappa^*$, where $\theta_N$ is the thermal state of mean photon number $N$. Let $E_F$ be entanglement of formation defined as the infimum of average marginal entropy over all pure-state probability decompositions, permitting continuous ensembles and arbitrary non-Gaussian vectors. Then $\rho(\kappa,N)$ is a normalized density and
--
--   $$E_F(\rho(\kappa,N))=E_F(\rho(\kappa,0))=g(\kappa-1),$$
--
--   where $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$ with $g(0)=0$. The entanglement is independent of the thermal input noise. At $\kappa=1$ the state is the separable product $\theta_N\otimes|0\rangle\langle0|$ and the value is zero.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 4, Eq. (13), repeated as (36)-(38), PDF pp.7-8

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

/-- PDF pp.4,7-8, (13),(36)-(38): unrestricted entanglement of formation of the
squeezed thermal family, independent of N. At kappa=1 the value is zero. -/
theorem squeezed_thermal_entanglement_formation
    (kappa N : ℝ) (hk : 1 ≤ kappa) (hN : 0 ≤ N) :
    IsDensity (squeezedThermal kappa N) ∧
    entanglementOfFormation (squeezedThermal kappa N) =
      entanglementOfFormation (squeezedThermal kappa 0) ∧
    entanglementOfFormation (squeezedThermal kappa N) = ENNReal.ofReal (thermalEntropyBits (kappa - 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
