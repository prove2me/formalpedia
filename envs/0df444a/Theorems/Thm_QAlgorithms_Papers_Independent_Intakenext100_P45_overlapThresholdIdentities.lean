-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_overlapThresholdIdentities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.overlapThresholdIdentities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:16:56.490788+00:00
-- url     : https://prove2.me/theorems/b7dccc27-988d-4e91-81b3-0514a51a78c5
-- title:
--   Lemma 5, overlap and threshold identities
-- statement:
--   For a nonorthogonal density pair and its spectral laws $p,q$, let $P_\rho,P_\sigma$ be support projections. Then
--
--   $$\psi_0=\operatorname{Tr}(\rho P_\sigma),\quad\psi_1=\operatorname{Tr}(\sigma P_\rho),$$
--   $$H(\widetilde p\|q)=S_\sigma(\rho\|\sigma),\quad H(\widetilde q\|p)=S_\rho(\sigma\|\rho).$$
--
--   Here $S_\sigma(\rho\|\sigma)=\operatorname{Re}\operatorname{Tr}[(\rho/\psi_0)(\log(\rho/\psi_0)-\log\sigma)P_\sigma]$, with the swapped definition for $S_\rho$. Conditional laws are extended by zero. The multiplication order and positive overlap normalization are retained.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 25, Lemma 5, overlap and threshold identities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.25,26: Lemma 5, overlap and threshold identities. Source correction: the last proof line on PDF p.26 swaps rho/psi0 with sigma/psi1; the defining displays and eigenvalue sum determine the stated orientation. Independent moderation required. -/
theorem overlapThresholdIdentities (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (D : SpectralPair rho sigma)
    (h0 : 0 < overlapMass (spectralP D) (spectralQ D))
    (h1 : 0 < overlapMass (spectralQ D) (spectralP D)) :
    overlapMass (spectralP D) (spectralQ D)=(rho*support sigma).trace.re ∧
    overlapMass (spectralQ D) (spectralP D)=(sigma*support rho).trace.re ∧
    kl (fun i => if 0 < spectralP D i ∧ 0 < spectralQ D i then
      spectralP D i / overlapMass (spectralP D) (spectralQ D) else 0) (spectralQ D) =
      ((supportConditionalEntropy rho sigma : ℝ) : EReal) ∧
    kl (fun i => if 0 < spectralP D i ∧ 0 < spectralQ D i then
      spectralQ D i / overlapMass (spectralQ D) (spectralP D) else 0) (spectralP D) =
      ((supportConditionalEntropy sigma rho : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
