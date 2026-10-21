-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_conditionalDeterminant
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.conditionalDeterminant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:17:35.893017+00:00
-- url     : https://prove2.me/theorems/4fd0e97c-7070-4cc4-87ec-9e6c3c9398fb
-- title:
--   The conditional determinant equals the one-copy determinant
-- statement:
--   Let $\rho$ be a normalized two-mode Gaussian density with arbitrary first moments and covariance $\Gamma_0=\begin{pmatrix}aI_2&cZ\\cZ&aI_2\end{pmatrix}$, where $Z=\operatorname{diag}(1,-1)$, $a\ge1$, and $0\le c\le\sqrt{a^2-1}$. Apply independent local Gaussian unitaries associated with arbitrary $S_A,S_B\in\mathrm{Sp}(4,\mathbb R)$, allowing displacements, to two identical copies. Selectively homodyne $A_2,B_2$ and retain $A_1,B_1$; permitted local Gaussian unitary feedback may follow.
--
--   For every finite outcome and every covariance $\Gamma''$ associated with that actual final Gaussian density,
--   $$\det\Gamma''=\det\Gamma_0=(a^2-c^2)^2.$$
--   This is the invariant of the constructed two-copy output. It does not concern an arbitrary physical four-mode covariance, nor is a determinant invariance assumption imposed on the protocol.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 3, Lemma 3: invariant determinant of the conditional output

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

/-- PDF p.3, Lemma 3: Gamma'' is associated to the ACTUAL Eq.(1),(2)
conditional output, rather than an arbitrary physical covariance. Local
feedback is allowed because it preserves this determinant. The complete
initial determinant equality (a^2-c^2)^2 is included. -/
theorem conditionalDeterminant (rho : DensityKernel 2) (a c : ℝ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hca : c ≤ Real.sqrt (a ^ 2 - 1))
    (hrho : GaussianWithCovariance rho (initialCovariance a c)) (p : TwoCopyHomodyneProtocol)
    (y : Outcome) (sigma : DensityKernel 2)
    (houtcome : HomodyneOutcome (beforeMeasurement p rho) y sigma)
    (gammaOut : Cov 2) (hgammaOut : GaussianWithCovariance (afterFeedback p y sigma) gammaOut) :
    gammaOut.det = (initialCovariance a c).det ∧
      (initialCovariance a c).det = (a ^ 2 - c ^ 2) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
