-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_thermalOutputEntropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.thermalOutputEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:38:19.466586+00:00
-- url     : https://prove2.me/theorems/82988cd9-e4a6-4d5b-93b9-bc1d39d00121
-- title:
--   V.A, Eq.(5.48): thermal output and entropy
-- statement:
--   Let $N,k,N_c\ge0$ be finite, let $\rho_N$ be the full one-mode thermal density of mean photon number $N$, and let $T$ be the fixed noisy attenuator/amplifier. Put $N'_0=\max\{0,k^2-1\}+N_c$ and $N'=k^2N+N'_0$. Then the actual output is thermal, and its spectral entropy in bits satisfies
--
--   $$T(\rho_N)=\rho_{N'},\qquad H(\rho_N)=g(N),\qquad H(T(\rho_N))=g(N').$$
--
--   Here $g(x)=(x+1)\log_2(x+1)-x\log_2 x$, with $g(0)=0$. Both densities are realized as bounded trace-class operators, and both extended spectral entropies are finite. This identifies the thermal output and its entropy.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.A, Eq.(5.48): thermal output and entropy

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

/-- V.A, (5.48), p.10: actual thermal output and finite spectral entropies. -/
theorem thermalOutputEntropy (N k Nc : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    RealizedDensity (thermalInput N) ∧
    RealizedDensity (noisyChannel k Nc (thermalInput N)) ∧
    noisyChannel k Nc (thermalInput N) = thermalInput (outputOccupation N k Nc) ∧
    spectralEntropyBits (thermalInput N) = ENNReal.ofReal (bosonicEntropy N) ∧
    spectralEntropyBits (noisyChannel k Nc (thermalInput N)) =
      ENNReal.ofReal (bosonicEntropy (outputOccupation N k Nc)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
