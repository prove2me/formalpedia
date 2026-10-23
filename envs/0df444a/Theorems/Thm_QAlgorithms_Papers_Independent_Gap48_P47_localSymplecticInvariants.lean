-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_localSymplecticInvariants
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.localSymplecticInvariants
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:10:55.859237+00:00
-- url     : https://prove2.me/theorems/92b9ffcc-16ee-415c-ba99-54b645694334
-- title:
--   Four local symplectic determinant invariants
-- statement:
--   Let $\rho$ be a normalized Gaussian state of two complete oscillators, with finite second moments and covariance
--   $$
--   \Gamma=\begin{pmatrix}A_1&B\\B^{\mathsf T}&A_2\end{pmatrix}
--   $$
--   in the vacuum-$I$, $\hbar=1$ convention. For real one-mode matrices $S_1,S_2$ satisfying $S_j^{\mathsf T}JS_j=J$, put $S=S_1\oplus S_2$ and $\widetilde\Gamma=S^{\mathsf T}\Gamma S$, with corresponding blocks $\widetilde A_1,\widetilde A_2,\widetilde B$. Then all four identities hold:
--   $$
--   \det\widetilde A_1=\det A_1,\qquad
--   \det\widetilde A_2=\det A_2,\qquad
--   \det\widetilde B=\det B,\qquad
--   \det\widetilde\Gamma=\det\Gamma.
--   $$
--   Here $J=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$ and every determinant is a matrix determinant.
--
--   These invariants supply the data used to compute the associated normal-form vector.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 4, Note [13]

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2 and p.4 note [13]: all four determinant invariants are preserved
by every local S1 direct-sum S2 in the source's passive convention. -/
theorem localSymplecticInvariants (rho : TwoModeGaussianDensity) (S1 S2 : Cov 1)
    (hS1 : S1.transpose * interleavedSymplecticForm 1 * S1 =
      interleavedSymplecticForm 1)
    (hS2 : S2.transpose * interleavedSymplecticForm 1 * S2 =
      interleavedSymplecticForm 1) :
    let changed := localCongruence rho.covariance S1 S2
    (modeCovarianceBlock changed 0 0).det =
      (modeCovarianceBlock rho.covariance 0 0).det ∧
    (modeCovarianceBlock changed 1 1).det =
      (modeCovarianceBlock rho.covariance 1 1).det ∧
    (modeCovarianceBlock changed 0 1).det =
      (modeCovarianceBlock rho.covariance 0 1).det ∧
    changed.det = rho.covariance.det := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
