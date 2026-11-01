-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_balancedGapBits
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.balancedGapBits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:07:21.608988+00:00
-- url     : https://prove2.me/theorems/f1487ee3-d97b-4ec6-a207-617adca11603
-- title:
--   Uniform 0.06-bit gap after Eq. (9)
-- statement:
--   All capacities below are unassisted operational capacities: finite message codes may use arbitrary mixed signal states entangled across channel uses and arbitrary collective output POVMs. The uniform-message average decoding error vanishes at all sufficiently large blocklengths. The constraint is ensemble-average total input photon number at most $nN$ for $n$ uses. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and use nats unless bits are specified.
--
--   For all $N_E,N\ge0$, let $U_{1/2}=g((N+N_E)/2)-\ln(1+e^{g(N_E)})+\ln2$ and $L_{1/2}=g((N+N_E)/2)-g(N_E/2)$. Then
--   $$\frac{U_{1/2}-L_{1/2}}{\ln2}\le0.06.$$
--   Thus the explicit balanced upper and coherent-signal lower bounds differ by at most $0.06$ bits uniformly in both photon means. The statement compares numerical bounds on capacity.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 3, Uniform 0.06-bit gap after Eq. (9)

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

/-- PDF p.3, sentence after (9): the balanced numerical upper bound minus
the Holevo coherent-signal lower bound is at most 0.06 bits, uniformly over
both photon means. This compares explicit bounds, not capacity with itself. -/
theorem balancedGapBits (NE N : ℝ) (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    balancedThermalUpperNats NE N / Real.log 2 -
      coherentSignalRateBits (1 / 2) NE N ≤ (6 / 100 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
