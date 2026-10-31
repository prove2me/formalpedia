-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_spectralPairIdentities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.spectralPairIdentities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:58:42.978615+00:00
-- url     : https://prove2.me/theorems/9772dc61-add5-40c7-9462-ad0ade19214f
-- title:
--   Proposition 1, spectral-pair identities
-- statement:
--   Choose complete orthonormal eigenbases $x_i,y_j$ of density operators $\rho,\sigma$, with eigenvalues $\lambda_i,\mu_j$. Set $p_{ij}=\lambda_i|\langle x_i,y_j\rangle|^2$ and $q_{ij}=\mu_j|\langle x_i,y_j\rangle|^2$. For every real $s$,
--
--   $$\operatorname{Tr}(\rho^{1-s}\sigma^s)=\sum_{i,j}p_{ij}^{1-s}q_{ij}^s,\qquad S(\rho\|\sigma)=H(p\|q).$$
--
--   Zero powers are unital; negative powers vanish on the kernel. Relative entropy is infinite on support failure. The construction retains choices within degenerate eigenspaces.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 10, Proposition 1, spectral-pair identities

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

/-- arXiv:0708.4282v1, PDF pp.9,10: Proposition 1, spectral-pair identities. -/
theorem spectralPairIdentities (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (D : SpectralPair rho sigma) :
    (∀ s : ℝ, chernoffOverlap rho sigma s = classicalOverlap (spectralP D) (spectralQ D) s) ∧
    relativeEntropy rho sigma = kl (spectralP D) (spectralQ D) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
