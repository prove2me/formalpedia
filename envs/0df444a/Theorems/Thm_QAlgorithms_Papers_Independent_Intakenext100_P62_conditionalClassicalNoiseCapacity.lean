-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_conditionalClassicalNoiseCapacity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.conditionalClassicalNoiseCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:10:44.952466+00:00
-- url     : https://prove2.me/theorems/dfbac0b8-86d6-472c-82d7-c89ce7b97efd
-- title:
--   Lemma A.2: conditional classical additive-noise bounds and gap
-- statement:
--   All capacities below are unassisted operational capacities: finite message codes may use arbitrary mixed signal states entangled across channel uses and arbitrary collective output POVMs. The uniform-message average decoding error vanishes at all sufficiently large blocklengths. The constraint is ensemble-average total input photon number at most $nN$ for $n$ uses. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and use nats unless bits are specified.
--
--   Assume the universal general quantum EPI for all positive mode counts, arbitrary independent states and all transmissivities, with nats entropy. For all finite photon increments $
--   u\ge0$ and budgets $N\ge0$, let $\mathcal E_
--   u$ be circular Gaussian displacement noise adding mean photon number $
--   u$, and the identity when $
--   u=0$. Set $L=g(N+
--   u)-g(
--   u)$ and $U=g(N+
--   u)-\ln(1+e
--   u)$. Then
--   $$L\le C(\mathcal E_
--   u,N)\le U,\qquad U-L\le0.11,\qquad\frac{U-L}{\ln2}\le0.16.$$
--   The two decimal bounds are in nats and bits respectively. Here $e
--   u$ means the product $e\cdot
--   u$. This is the full conditional capacity sandwich and uniform gap of Lemma A.2.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 9, Lemma A.2: conditional classical additive-noise bounds and gap

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

/-- PDF p.9, Lemma A.2, (A15)–(A16): conditional classical Gaussian-noise
capacity sandwich and both uniform numerical gap bounds. The logarithm contains
1+e*nu, not 1+exp(nu). Noise nu is the finite photon increment; nu=0 is included.
The numerical differences are upper-minus-lower, in nats and bits respectively. -/
theorem conditionalClassicalNoiseCapacity (hEPI : GeneralQuantumEPI)
    (nu N : ℝ) (hnu : 0 ≤ nu) (hN : 0 ≤ N) :
    ENNReal.ofReal (g (N + nu) - g nu) ≤
      photonCapacityNats (classicalNoiseKernel nu) N ∧
    photonCapacityNats (classicalNoiseKernel nu) N ≤
      ENNReal.ofReal (g (N + nu) - Real.log (1 + Real.exp 1 * nu)) ∧
    (g (N + nu) - Real.log (1 + Real.exp 1 * nu)) -
      (g (N + nu) - g nu) ≤ (11 / 100 : ℝ) ∧
    ((g (N + nu) - Real.log (1 + Real.exp 1 * nu)) -
      (g (N + nu) - g nu)) / Real.log 2 ≤ (16 / 100 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
