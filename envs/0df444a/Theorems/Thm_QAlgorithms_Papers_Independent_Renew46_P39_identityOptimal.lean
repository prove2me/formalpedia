-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_identityOptimal
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.identityOptimal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:14:34.911124+00:00
-- url     : https://prove2.me/theorems/53d7f4c2-4be4-4144-ad82-940f91df6f04
-- title:
--   Identity preprocessing and feedback attain equality
-- statement:
--   Let $\rho$ be any normalized two-mode Gaussian density with arbitrary first moments and covariance $\Gamma_0=\begin{pmatrix}aI_2&cZ\\cZ&aI_2\end{pmatrix}$, where $Z=\operatorname{diag}(1,-1)$, $a\ge1$, and $0\le c\le\sqrt{a^2-1}$. Use two identical independent copies in the restricted Fig.1 protocol, with identity preprocessing and identity feedback. Measure the unused modes $A_2,B_2$ by homodyne detection, retaining $A_1,B_1$.
--
--   For every finite pair of real outcomes $y$, the conditional density exists. Every resulting final density $\tau_y$ satisfies
--   $$\tau_y=\rho,\qquad E_N(\tau_y)=E_N(\rho),\qquad E_N(\omega)=\log_2\|\omega^{T_A}\|_1.$$
--   The partial transpose of $\rho$ has finite trace norm at least one. This gives equality attainment within the restricted protocol family; together with the no-distillation theorem it explains the stated optimality. No optimization over arbitrary LOCC protocols is asserted.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 1, Unnumbered optimality: doing nothing loses no entanglement (p.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39

noncomputable section

open Filter

open scoped BigOperators Topology ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P39

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClass traceSize rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl weylArgument CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm isSymplectic)

open QAlgorithms.Papers.Independent.Dependency50.P10
  (physicalCovariance supportInverse)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

/-- PDF p.1, unnumbered optimality sentence: identity preprocessing and feedback
mean keeping the first independent pair and measuring the second. The output
is exactly rho at every finite outcome, attaining equality only in Fig.1. -/
theorem identityOptimal (rho : DensityKernel 2) (a c : ℝ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hca : c ≤ Real.sqrt (a ^ 2 - 1))
    (hrho : GaussianWithCovariance rho (initialCovariance a c)) :
    FinitePartialTranspose rho ∧ ∀ y : Outcome,
      HomodyneOutcome (beforeMeasurement identityProtocol rho) y rho ∧
      (∀ sigma : DensityKernel 2,
        HomodyneOutcome (beforeMeasurement identityProtocol rho) y sigma →
        afterFeedback identityProtocol y sigma = rho ∧
        oscillatorLogNegativity (afterFeedback identityProtocol y sigma) = oscillatorLogNegativity rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
