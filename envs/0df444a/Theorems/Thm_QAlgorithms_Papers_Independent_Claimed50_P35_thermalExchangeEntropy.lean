-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_thermalExchangeEntropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.thermalExchangeEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:40:02.738679+00:00
-- url     : https://prove2.me/theorems/239a66ac-bae9-4979-abdc-c44d5766dd90
-- title:
--   V.A, Eq.(5.50): thermal entropy exchange
-- statement:
--   Let $N,k,N_c\ge0$, $N'=k^2N+\max\{0,k^2-1\}+N_c$, and $D=\sqrt{(N+N'+1)^2-4k^2N(N+1)}$. Construct the normalized pure thermal purification $|\psi_N\rangle=\sum_n\sqrt{p_n}|n,n\rangle$, where $p_n=N^n/(N+1)^{n+1}$, and apply the actual channel $T$ to its first factor. The entropy exchange is the spectral entropy of this normalized joint output and equals
--
--   $$H(\rho_N,T)=g\!\left(\frac{D+N'-N-1}{2}\right)+g\!\left(\frac{D-N'+N-1}{2}\right).$$
--
--   The formula is finite and in bits, including vacuum and identity endpoints. The reference marginal equals $\rho_N$. This is an identity for an actual output density, rather than an assigned covariance entropy.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.A, Eq.(5.50): thermal entropy exchange

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- V.A, (5.50), p.10: entropy exchange is the entropy of the actual
normalized joint channel output on a pure thermal purification. -/
theorem thermalExchangeEntropy (N k Nc : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    RealizedDensity (thermalPurificationDensity N) ∧
    partialRight (thermalPurificationDensity N) = thermalInput N ∧
    RealizedDensity (thermalExchangeOutput N k Nc) ∧
    spectralEntropyBits (thermalExchangeOutput N k Nc) = ENNReal.ofReal
      (bosonicEntropy ((exchangeD N k Nc + outputOccupation N k Nc - N - 1) / 2) +
       bosonicEntropy ((exchangeD N k Nc - outputOccupation N k Nc + N - 1) / 2)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
