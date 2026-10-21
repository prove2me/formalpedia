-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_exchangeSpectrum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.exchangeSpectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:39:09.185621+00:00
-- url     : https://prove2.me/theorems/7faf838b-23ce-4e50-a663-8e5a63c3e88d
-- title:
--   V.A, Eq.(5.49): exchange covariance spectrum
-- statement:
--   For finite $N,k,N_c\ge0$, write $N'=k^2N+\max\{0,k^2-1\}+N_c$ and $D=\sqrt{(N+N'+1)^2-4k^2N(N+1)}$. The complex representation of the exchange covariance operator is
--
--   $$M=\begin{pmatrix}i(N'+1/2)&k\sqrt{N(N+1)}\\k\sqrt{N(N+1)}&-i(N+1/2)\end{pmatrix}.$$
--
--   Its characteristic polynomial factors with roots
--
--   $$\lambda_\pm=\tfrac i2(N'-N\pm D),\qquad (D\pm(N'-N)-1)/2\ge0.$$
--
--   The factorization includes algebraic multiplicities. This two-dimensional complex representation accounts for paired eigenvalues in the real four-dimensional matrix; no entropy multiplicity is doubled.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.A, Eq.(5.49): exchange covariance spectrum

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

/-- V.A, (5.49), p.10: exact roots with multiplicities and nonnegative
occupation parameters. No doubling of the two g terms occurs. -/
theorem exchangeSpectrum (N k Nc : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    (exchangeMatrix N k Nc).charpoly =
      (Polynomial.X - Polynomial.C (Complex.I *
        (((outputOccupation N k Nc - N + exchangeD N k Nc) / 2 : ℝ) : ℂ))) *
      (Polynomial.X - Polynomial.C (Complex.I *
        (((outputOccupation N k Nc - N - exchangeD N k Nc) / 2 : ℝ) : ℂ))) ∧
    0 ≤ (exchangeD N k Nc + outputOccupation N k Nc - N - 1) / 2 ∧
    0 ≤ (exchangeD N k Nc - outputOccupation N k Nc + N - 1) / 2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
