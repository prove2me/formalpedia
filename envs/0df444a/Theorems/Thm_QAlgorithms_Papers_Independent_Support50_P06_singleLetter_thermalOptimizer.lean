-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_singleLetter_thermalOptimizer
-- name    : QAlgorithms.Papers.Independent.Support50.P06.singleLetter_thermalOptimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:30:09.454642+00:00
-- url     : https://prove2.me/theorems/7797e2c4-ab0b-4057-9047-b76b66059e75
-- title:
--   Conditional attained thermal coherent-information maximum
-- statement:
--   Assume global minimum output entropy conjecture 2. Let $1/2<\eta\le1$ and $\bar N\ge0$ be finite. For arbitrary normalized single-mode input states with mean photons at most $\bar N$, define $I_c(\rho)=S(\mathcal L_\eta(\rho))-S(\mathcal E_\eta(\rho))$ using the two marginals of the fixed vacuum dilation. Entropies are in nats. Then
--
--   $$C_p(\eta,\bar N)=Q^{(1)}(\eta,\bar N)=\max_{\operatorname{Tr}(\rho\hat n)\le\bar N} I_c(\rho)=g(\eta\bar N)-g((1-\eta)\bar N).$$
--
--   Both receiver entropies are finite for every feasible input. The normalized thermal input of mean exactly $\bar N$ attains this maximum, Bob's output is thermal of mean $\eta\bar N$, and the input is the isotropic Gaussian coherent mixture of variance $\bar N$ (vacuum at zero). The optimization has no Gaussian restriction.
--
--   This identifies $Q^{(1)}$ as a constrained coherent-information optimization; it does not define an operational quantum transmission capacity.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, (12): conditional attained coherent-information maximum

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (12): attained, unrestricted coherent-information optimum under
mean photons <=Nbar, conditional on global MOE2. Printed Gaussian variance K
reuses Bob's entropy variable; changed to Alice variance Nbar as fixed by (10)
and the theorem's own prior. Bob's thermal mean is eta*Nbar, not K. Finite
receiver entropy is concluded for every feasible input; it is not assumed. -/
theorem singleLetter_thermalOptimizer (hmoe : StrongConjecture2)
    (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta_one : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    coherentInformationMaximum 1 eta Nbar =
      ((g (eta * Nbar) - g ((1 - eta) * Nbar) : ℝ) : EReal) ∧
    holevoMessagePrivacyCapacityNats 1 eta Nbar = ENNReal.ofReal (g (eta * Nbar) - g ((1 - eta) * Nbar)) ∧
    IsDensity (identicalThermalKernel 1 Nbar) ∧
    totalEnergy (identicalThermalKernel 1 Nbar) = ENNReal.ofReal Nbar ∧
    pureLoss 1 eta (identicalThermalKernel 1 Nbar) = identicalThermalKernel 1 (eta * Nbar) ∧
    coherentMixture Nbar = identicalThermalKernel 1 Nbar ∧
    vacuumLossCoherentInformationNats eta (identicalThermalKernel 1 Nbar) =
      g (eta * Nbar) - g ((1 - eta) * Nbar) ∧
    (∀ rho : State (NumberString 1), totalEnergy rho.coefficients ≤ ENNReal.ofReal Nbar →
      spectralEntropyNats (pureLoss 1 eta rho.coefficients) ≠ ⊤ ∧
      spectralEntropyNats ((charlieMarginal (broadcast 1 eta rho.coefficients))) ≠ ⊤ ∧
      vacuumLossCoherentInformationNats eta rho.coefficients ≤ g (eta * Nbar) - g ((1 - eta) * Nbar)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
