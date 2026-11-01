-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_fisherConvexityClosed
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.fisherConvexityClosed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:08:28.618083+00:00
-- url     : https://prove2.me/theorems/2911b536-7ed9-46bd-ae3f-292ced4253d4
-- title:
--   Convexity of total displacement Fisher information, Eq. (15)
-- statement:
--   Let $n\ge1$ and let $\rho_X,\rho_Y$ be arbitrary normalized states on the full $n$-mode bosonic Fock spaces. Their joint input is the product $\rho_X\otimes\rho_Y$; entanglement within either input is unrestricted. Let $B_\lambda$ retain the port with quadratures $\sqrt\lambda R_X+\sqrt{1-\lambda}R_Y$. Write $S$ for extended nonnegative von Neumann entropy in nats.
--
--   For each state, let $\widetilde J$ be the sum of its divergence-based displacement Fisher information over all $2n$ canonical directions, without averaging. Require local finiteness and genuine second-derivative regularity for every directional divergence of both inputs and their output. Then, for all $0\le\lambda\le1$,
--   $$\widetilde J(B_\lambda(\rho_X\otimes\rho_Y))\le\lambda\widetilde J(\rho_X)+(1-\lambda)\widetilde J(\rho_Y).$$
--   The same displacement scale is used throughout. This is convexity under beam-splitter mixing on the finite Fisher domain.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 5, Convexity of total displacement Fisher information, Eq. (15)

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

/-- PDF p.5, (15): total displacement Fisher convexity under beam-splitter
mixing, including lambda=0,1. Every one of the 2n directional second derivatives
is in its genuine locally finite differentiability domain for both inputs and
output. A common displacement or bits/nats rescaling cancels from this inequality. -/
theorem fisherConvexityClosed {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (rhoX rhoY : State (FockIndex n))
    (hX : TotalFisherRegular rhoX.coefficients)
    (hY : TotalFisherRegular rhoY.coefficients)
    (hOut : TotalFisherRegular (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients))) :
    totalFisher (beamSplitter lam (productCoeff rhoX.coefficients rhoY.coefficients)) ≤
      lam * totalFisher rhoX.coefficients +
        (1 - lam) * totalFisher rhoY.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
