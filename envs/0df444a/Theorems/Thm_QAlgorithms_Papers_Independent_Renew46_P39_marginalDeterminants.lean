-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_marginalDeterminants
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.marginalDeterminants
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:18:21.367993+00:00
-- url     : https://prove2.me/theorems/7be97be0-8b9f-4ef4-a34f-aadcadd49d53
-- title:
--   Both retained marginal determinants are bounded by the initial value
-- statement:
--   Let $\rho$ be a normalized two-mode Gaussian density with arbitrary first moments and covariance $\Gamma_0=\begin{pmatrix}aI_2&cZ\\cZ&aI_2\end{pmatrix}$, where $Z=\operatorname{diag}(1,-1)$, $a\ge1$, and $0\le c\le\sqrt{a^2-1}$. Run the restricted two-copy protocol with arbitrary independent local symplectic unitaries, displacements, selective homodyne measurement on $A_2,B_2$, and allowed local Gaussian unitary feedback.
--
--   At any finite outcome let $\Gamma''$ be the covariance of the actual retained state. Write $\Gamma''_A,\Gamma''_B$ for its principal $2\times2$ blocks on $A_1,B_1$, and $\Gamma_{0,A},\Gamma_{0,B}$ for the corresponding one-copy input blocks. Then
--   $$\det\Gamma''_A\le\det\Gamma_{0,A}=a^2,\qquad\det\Gamma''_B\le\det\Gamma_{0,B}=a^2.$$
--   Both inequalities and both initial equalities are part of the statement. The output association refers to the physical protocol, and the bounds are not assumed in the main no-distillation theorem.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 3, Lemma 4: principal marginal determinant bounds

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

/-- PDF p.3, Lemma 4, (12): both retained principal-marginal bounds and both
initial equalities, with the same two-copy and local-unitary scope as Lemma 3.
The proof's second reference to measuring A1 is read as A2. -/
theorem marginalDeterminants (rho : DensityKernel 2) (a c : ℝ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hca : c ≤ Real.sqrt (a ^ 2 - 1))
    (hrho : GaussianWithCovariance rho (initialCovariance a c)) (p : TwoCopyHomodyneProtocol)
    (y : Outcome) (sigma : DensityKernel 2)
    (houtcome : HomodyneOutcome (beforeMeasurement p rho) y sigma)
    (gammaOut : Cov 2) (hgammaOut : GaussianWithCovariance (afterFeedback p y sigma) gammaOut) :
    (modeCovarianceBlock gammaOut 0 0).det ≤
      (modeCovarianceBlock (initialCovariance a c) 0 0).det ∧
    (modeCovarianceBlock (initialCovariance a c) 0 0).det = a ^ 2 ∧
    (modeCovarianceBlock gammaOut 1 1).det ≤
      (modeCovarianceBlock (initialCovariance a c) 1 1).det ∧
    (modeCovarianceBlock (initialCovariance a c) 1 1).det = a ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
