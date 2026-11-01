-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_conditionalThermalCapacity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.conditionalThermalCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:09:56.213871+00:00
-- url     : https://prove2.me/theorems/67698226-8a8a-49a9-806f-021264de9802
-- title:
--   Conditional thermal capacity bound, Eq. (A14) = (A17), and 0.16-bit claim
-- statement:
--   All capacities below are unassisted operational capacities: finite message codes may use arbitrary mixed signal states entangled across channel uses and arbitrary collective output POVMs. The uniform-message average decoding error vanishes at all sufficiently large blocklengths. The constraint is ensemble-average total input photon number at most $nN$ for $n$ uses. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and use nats unless bits are specified.
--
--   Assume universally the general quantum EPI: for every positive mode count, all independent normalized full-Fock inputs and every $0\le\lambda\le1$, the output entropy power $e^{S/n}$ is at least the $\lambda,1-\lambda$ weighted sum of input entropy powers. Under this premise, for all thermal parameters $0\le\lambda\le1$, $N_E,N\ge0$, put
--   $$U_\lambda=g(\lambda N+(1-\lambda)N_E)-\ln(\lambda+(1-\lambda)e^{g(N_E)}),\qquad L_\lambda=g(\lambda N+(1-\lambda)N_E)-g((1-\lambda)N_E).$$
--   Then
--   $$C(\mathcal E_{\lambda,N_E},N)\le U_\lambda,\qquad \frac{U_\lambda-L_\lambda}{\ln2}\le0.16.$$
--   This retains both the conditional capacity inequality and its advertised uniform bit-gap consequence. The universal premise is not asserted as a theorem.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 9, Conditional thermal capacity bound, Eq. (A14) = (A17), and 0.16-bit claim

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P62

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P62

open scoped ENNReal BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (State productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (FockIndex)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g displacementNoiseChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)

open QAlgorithms.Papers.Independent.Bridge50.P28
  (classicalPhotonCapacityBits thermalNoiseChannelKernel coherentSignalRateBits)

open QAlgorithms.Papers.Independent.Next46.P17
  (beamSplitter bosonicEntropyPower diffusionChannel TotalFisherRegular totalFisher)

/-- PDF pp.4,7,9, (A14)/(A17): conditional thermal capacity upper bound
and advertised uniform 0.16-bit numerical gap from the Holevo lower bound.
The universal conjecture precedes every channel parameter; it is not inferred
from the proved balanced EPI. -/
theorem conditionalThermalCapacity (hEPI : GeneralQuantumEPI)
    (lam NE N : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    photonCapacityNats (thermalNoiseChannelKernel lam NE) N ≤
      ENNReal.ofReal (conjecturedThermalUpperNats lam NE N) ∧
    conjecturedThermalUpperNats lam NE N / Real.log 2 -
      coherentSignalRateBits lam NE N ≤ (16 / 100 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
