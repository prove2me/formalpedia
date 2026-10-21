-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_squeezingCannotIncrease
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.squeezingCannotIncrease
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:15:22.836562+00:00
-- url     : https://prove2.me/theorems/450afdaf-edb0-4949-812a-dfa36d9a448b
-- title:
--   The restricted protocol cannot increase two-mode vacuum squeezing
-- statement:
--   For $r\ge0$, let $\rho_r=|\psi_r\rangle\langle\psi_r|$ be the normalized two-mode squeezed vacuum on the full oscillator Hilbert space, where
--   $$|\psi_r\rangle=\frac1{\cosh r}\sum_{n=0}^{\infty}(\tanh r)^n|n,n\rangle.$$
--   Its vacuum-$I$ covariance has $a=\cosh(2r)$ and $c=\sinh(2r)$ in the opposite-sign correlation form. Apply the restricted Fig.1 protocol to two independent copies of $\rho_r$: arbitrary local two-mode Gaussian unitaries and displacements, homodyne measurement of the second modes, communication of both real outcomes, and local Gaussian unitary feedback.
--
--   If at any finite selective outcome the density after feedback is another two-mode squeezed vacuum $\rho_{r_{\rm out}}$, with $r_{\rm out}\ge0$, then
--   $$r_{\rm out}\le r.$$
--   Thus two identical squeezed vacua cannot produce a more strongly squeezed vacuum by the stated operations. The squeezing versus logarithmic-negativity relation is not assumed in the formal hypotheses.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 1, Unnumbered corollary: no increased two-mode vacuum squeezing (pp.1-2)

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

/-- PDF pp.1--2, unnumbered squeezing corollary, including the sentence
continuing onto p.2. Nonnegative r parametrizes the ACTUAL squeezed vacuum;
the relation between squeezing and E_N is not an assumed hypothesis. -/
theorem squeezingCannotIncrease (r rOut : ℝ) (hr : 0 ≤ r) (hrOut : 0 ≤ rOut)
    (p : TwoCopyHomodyneProtocol) (y : Outcome) (sigma : DensityKernel 2)
    (houtcome : HomodyneOutcome (beforeMeasurement p (squeezedVacuum r)) y sigma)
    (hout : afterFeedback p y sigma = squeezedVacuum rOut) :
    rOut ≤ r := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
