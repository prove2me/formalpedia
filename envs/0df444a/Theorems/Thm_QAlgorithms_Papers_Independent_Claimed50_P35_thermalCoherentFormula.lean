-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_thermalCoherentFormula
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.thermalCoherentFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:42:46.991506+00:00
-- url     : https://prove2.me/theorems/f551c646-08e9-4a76-a04e-dc723afb4c56
-- title:
--   V.B, Eq.(5.54): thermal coherent information
-- statement:
--   Let $N,k,N_c\ge0$ be finite. For the actual thermal input $\rho_N$ and noisy channel $T$, write $N'=k^2N+\max\{0,k^2-1\}+N_c$ and $D=\sqrt{(N+N'+1)^2-4k^2N(N+1)}$. Both the output entropy and the exchange entropy are finite, and
--
--   $$J(\rho_N,T)=g(N')-g\!\left(\frac{D+N'-N-1}{2}\right)-g\!\left(\frac{D-N'+N-1}{2}\right).$$
--
--   Here $J=H(T(\rho_N))-H(\rho_N,T)$ and $g$ is the thermal entropy in bits. Negative values are allowed. This is a thermal-input evaluation, with no Gaussian or all-state supremum assertion.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 11, V.B, Eq.(5.54): thermal coherent information

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

/-- V.B, (5.54), p.11: thermal-input value, not an optimum; negative J is
allowed. Both entropies are finite before conversion to real numbers. -/
theorem thermalCoherentFormula (N k Nc : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    spectralEntropyBits (noisyChannel k Nc (thermalInput N)) ≠ ⊤ ∧
    spectralEntropyBits (thermalExchangeOutput N k Nc) ≠ ⊤ ∧
    thermalCoherentInformation N k Nc = bosonicEntropy (outputOccupation N k Nc) -
      bosonicEntropy ((exchangeD N k Nc + outputOccupation N k Nc - N - 1) / 2) -
      bosonicEntropy ((exchangeD N k Nc - outputOccupation N k Nc + N - 1) / 2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
