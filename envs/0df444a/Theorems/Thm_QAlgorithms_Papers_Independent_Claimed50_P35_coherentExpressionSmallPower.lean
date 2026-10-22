-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_coherentExpressionSmallPower
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.coherentExpressionSmallPower
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:40:26.796425+00:00
-- url     : https://prove2.me/theorems/7d6519e2-f270-40ae-8b2a-b24ed23faca6
-- title:
--   V.A: small-power achieved-rate asymptotic
-- statement:
--   Fix $k>0$ and $N_c\ge0$ such that $N'_0=\max\{0,k^2-1\}+N_c>0$. For the underlined scalar rate expression $\underline C_1(N)=g(k^2N+N'_0)-g(N'_0)$, one has the positive one-sided equivalent
--
--   $$\lim_{N\downarrow0}\frac{\underline C_1(N)}{Nk^2\log_2((N'_0+1)/N'_0)}=1.$$
--
--   The parameters remain fixed in the limit. This evaluates the expression displayed by the source; it does not claim that the coherent ensemble optimizes the one-shot capacity.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.A: small-power achieved-rate asymptotic

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

/-- V.A, p.10: small-power equivalent of the underlined rate expression.
Parameters precede the one-sided limit; zero comparison and log0 are excluded. -/
theorem coherentExpressionSmallPower (k Nc : ℝ) (hk : 0 < k) (hNc : 0 ≤ Nc)
    (hv : 0 < vacuumOutput k Nc) :
    Tendsto (fun N : ℝ => coherentGaussianExpression N k Nc /
      (N * k ^ 2 * Real.logb 2 ((vacuumOutput k Nc + 1) / vacuumOutput k Nc)))
      (𝓝[>] 0) (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
