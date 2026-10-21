-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_generalizedThermalNorm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.generalizedThermalNorm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:35:24.703611+00:00
-- url     : https://prove2.me/theorems/f0a0c294-f333-403e-afce-0922ec02db1c
-- title:
--   IV.D, Eq.(4.46): generalized thermal trace norm
-- statement:
--   For $\gamma>0$, define the full Fock-space diagonal operator
--
--   $$\rho_\gamma=\frac1{\gamma+1/2}\sum_{n=0}^{\infty}\left(\frac{\gamma-1/2}{\gamma+1/2}\right)^n|n\rangle\langle n|.$$
--
--   This operator is trace class, and its trace norm is
--
--   $$\|\rho_\gamma\|_1=\frac1{\gamma+1/2}\sum_{n=0}^{\infty}\left|\frac{\gamma-1/2}{\gamma+1/2}\right|^n=\max\{1,(2\gamma)^{-1}\}.$$
--
--   Below $\gamma=1/2$ it need not be a density. This evaluates the generalized thermal representative without imposing positivity.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 9, IV.D, Eq.(4.46): generalized thermal trace norm

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

/-- IV.D, (4.46), p.9: gamma>0 ensures trace class; gamma<1/2 is not a density. -/
theorem generalizedThermalNorm (gamma : ℝ) (hgamma : 0 < gamma) :
    IsTraceClass (generalizedThermal gamma) ∧
    traceSize (generalizedThermal gamma) = ENNReal.ofReal (max 1 (1 / (2 * gamma))) ∧
    (1 / (gamma + 1 / 2)) *
      (∑' n : ℕ, |(gamma - 1 / 2) / (gamma + 1 / 2)| ^ n) =
      max 1 (1 / (2 * gamma)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
