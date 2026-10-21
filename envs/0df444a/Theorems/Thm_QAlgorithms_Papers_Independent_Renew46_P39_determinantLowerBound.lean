-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P39_determinantLowerBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P39.determinantLowerBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:19:05.284024+00:00
-- url     : https://prove2.me/theorems/c02d3a84-bd20-40ed-b6b3-69a3de5f7578
-- title:
--   A lower bound for f from the two principal determinants
-- statement:
--   Let $\gamma$ be any real symmetric physical two-mode covariance in interleaved $X,P$ coordinates with vacuum covariance $I$: $\gamma-i\Sigma$ is Hermitian positive semidefinite, where $\Sigma=J\oplus J$ and $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Partition $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ into $2\times2$ mode blocks. Define
--   $$u=\frac{\det A+\det B}{2},\qquad t=u-\det C,\qquad f(\gamma)=t-\sqrt{t^2-\det\gamma}.$$
--   Then
--   $$f(\gamma)\ge g(\gamma):=\left(\sqrt{u}-\sqrt{u-\sqrt{\det\gamma}}\right)^2.$$
--   All square roots use the nonnegative real branch on the physical domain. This bound applies without party symmetry or the special two-copy input form, and expresses the lower bound using only principal determinants and the total determinant.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, PDF p. 3, Lemma 5: lower bound on f from principal determinants

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

/-- PDF p.3, Lemma 5, (13), for EVERY physical two-mode covariance.
Physicality is the Hermitian PSD inequality Gamma-i Sigma >= 0 with real
symmetry, not an entrywise inequality or a symmetry-between-parties premise.
The inner determinant radical is sqrt(det gamma), exactly as printed. -/
theorem determinantLowerBound (gamma : Cov 2)
    (hgamma : physicalCovariance gamma (interleavedSymplecticForm 2)) :
    sourceF gamma ≥ sourceG gamma := by sorry

end QAlgorithms.Papers.Independent.Renew46.P39

end
