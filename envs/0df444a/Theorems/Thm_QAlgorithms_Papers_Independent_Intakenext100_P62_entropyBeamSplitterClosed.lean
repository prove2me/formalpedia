-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P62_entropyBeamSplitterClosed
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P62.entropyBeamSplitterClosed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:06:41.989989+00:00
-- url     : https://prove2.me/theorems/91a6c75f-5e59-4060-9f2b-5bc697e20e96
-- title:
--   Linear quantum entropy power inequality, Eq. (4) = Eq. (18)
-- statement:
--   Let $n\ge1$ and let $\rho_X,\rho_Y$ be arbitrary normalized states on the full $n$-mode bosonic Fock spaces. Their joint input is the product $\rho_X\otimes\rho_Y$; entanglement within either input is unrestricted. Let $B_\lambda$ retain the port with quadratures $\sqrt\lambda R_X+\sqrt{1-\lambda}R_Y$. Write $S$ for extended nonnegative von Neumann entropy in nats.
--
--   For every $0\le\lambda\le1$,
--   $$S(B_\lambda(\rho_X\otimes\rho_Y))\ge\lambda S(\rho_X)+(1-\lambda)S(\rho_Y).$$
--   No energy, entropy-finiteness, Gaussianity or smoothness assumption is imposed. Infinite entropy is retained, with $0\cdot\infty=0$. This controls entropy production under physical mixing, including the endpoints.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, PDF p. 2, Linear quantum entropy power inequality, Eq. (4) = Eq. (18)

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

/-- PDF pp.2,7, (4)/(18): linear quantum EPI for arbitrary independent
normalized full n-mode states. No Gaussianity, finite entropy, finite energy or
smoothness hypothesis is imposed. ENNReal uses 0*infinity=0 at lambda=0,1. -/
theorem entropyBeamSplitterClosed {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (rhoX rhoY : State (FockIndex n)) :
    ENNReal.ofReal lam * extendedEntropyNats rhoX.coefficients +
      ENNReal.ofReal (1 - lam) * extendedEntropyNats rhoY.coefficients ≤
    extendedEntropyNats (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P62

end
