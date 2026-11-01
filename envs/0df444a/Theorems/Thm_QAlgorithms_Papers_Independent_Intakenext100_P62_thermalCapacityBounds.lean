-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_thermalCapacityBounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.thermalCapacityBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:05:51.833489+00:00
-- url     : https://prove2.me/theorems/2d683ca9-da47-4db9-8756-c680a941e225
-- title:
--   Paper-level main capacity bounds: Lemma A.1, Eqs. (8)–(9), (A1)–(A2)
-- statement:
--   All capacities below are unassisted operational capacities: finite message codes may use arbitrary mixed signal states entangled across channel uses and arbitrary collective output POVMs. The uniform-message average decoding error vanishes at all sufficiently large blocklengths. The constraint is ensemble-average total input photon number at most $nN$ for $n$ uses. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and use nats unless bits are specified.
--
--   For every transmissivity $0\le\lambda\le1$, environment photon mean $N_E\ge0$ and input photon budget $N\ge0$, the memoryless channel has a fresh independent thermal environment each use and satisfies
--   $$C(\mathcal E_{\lambda,N_E},N)\le g(\lambda N+(1-\lambda)N_E)-(1-\lambda)g(N_E).$$
--   For $\lambda=1/2$ it additionally satisfies
--   $$C(\mathcal E_{1/2,N_E},N)\le g((N+N_E)/2)-\ln(1+e^{g(N_E)})+\ln2.$$
--   These are the paper's two explicit entropy-power capacity bounds.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 8, Paper-level main capacity bounds: Lemma A.1, Eqs. (8)–(9), (A1)–(A2)

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

/-- PDF pp.3,8–9, (8)–(9), Lemma A.1, (A1)–(A2): both new capacity bounds,
in nats, including all zero-energy and transmissivity endpoints. The balanced
clause concerns the same environment and input budget. -/
theorem thermalCapacityBounds (lam NE N : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    photonCapacityNats (thermalNoiseChannelKernel lam NE) N ≤
      ENNReal.ofReal (g (lam * N + (1 - lam) * NE) - (1 - lam) * g NE) ∧
    (lam = 1 / 2 →
      photonCapacityNats (thermalNoiseChannelKernel lam NE) N ≤
        ENNReal.ofReal (balancedThermalUpperNats NE N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
