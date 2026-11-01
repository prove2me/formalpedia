-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_generalEnvironmentCapacity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.generalEnvironmentCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:07:51.191731+00:00
-- url     : https://prove2.me/theorems/d30c3eae-6b75-44cb-81f6-40746e2acb5e
-- title:
--   Figure 3: capacity bound for arbitrary beam-splitter environment
-- statement:
--   All capacities below are unassisted operational capacities: finite message codes may use arbitrary mixed signal states entangled across channel uses and arbitrary collective output POVMs. The uniform-message average decoding error vanishes at all sufficiently large blocklengths. The constraint is ensemble-average total input photon number at most $nN$ for $n$ uses. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and use nats unless bits are specified.
--
--   Fix $0\le\lambda\le1$, $N\ge0$ and any normalized one-mode environment state $\sigma$. Each use mixes the signal with a fresh independent copy of $\sigma$ and retains the plus port, defining $\mathcal E$. Define $S_{\max}(\mathcal E,N)$ as the supremum of output entropy over normalized one-mode inputs of mean photons at most $N$. Then
--   $$C(\mathcal E,N)+(1-\lambda)S(\sigma)\le S_{\max}(\mathcal E,N).$$
--   This is the caption's subtraction bound whenever finite. The additive extended interpretation also retains environments of infinite entropy, and adds no attainment or finite-energy assumption on the environment.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 4, Figure 3: capacity bound for arbitrary beam-splitter environment

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

/-- PDF p.4, Fig.3 caption (derived on p.8): capacity for an arbitrary fixed
one-mode environment. This additive form agrees with the displayed subtraction
when finite and avoids infinity-minus-infinity for infinite environment entropy.
At lambda=1 the environment contribution is zero, even at infinite entropy. -/
theorem generalEnvironmentCapacity (lam N : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hN : 0 ≤ N) (sigma : State ℕ) :
    photonCapacityNats (oneModeBeamChannel lam sigma) N +
      ENNReal.ofReal (1 - lam) * extendedEntropyNats sigma.coefficients ≤
    maximumOutputEntropyNats (oneModeBeamChannel lam sigma) N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
