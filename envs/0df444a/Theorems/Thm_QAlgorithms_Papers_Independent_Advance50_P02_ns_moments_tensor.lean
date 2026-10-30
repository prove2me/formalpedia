-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_ns_moments_tensor
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.ns_moments_tensor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:27:56.913989+00:00
-- url     : https://prove2.me/theorems/3faa4809-4e54-4376-9c00-feaf26034f09
-- title:
--   NS moment and tensor identities
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized, $\sigma\ge0$, and $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Choose arbitrary full orthonormal spectral decompositions $\rho=\sum_x r_x|v_x\rangle\langle v_x|$ and $\sigma=\sum_y s_y|u_y\rangle\langle u_y|$. Define $P(x,y)=r_x|\langle v_x,u_y\rangle|^2$ and $Q(x,y)=s_y|\langle v_x,u_y\rangle|^2$. With centered variances,
--   $$D(P\Vert Q)=D(\rho\Vert\sigma),\qquad V(P\Vert Q)=V(\rho\Vert\sigma).$$
--   Using the product eigenbases for tensor powers, for every $n$,
--   $$P_{\rho^{\otimes n},\sigma^{\otimes n}}=P^{\otimes n},\qquad Q_{\rho^{\otimes n},\sigma^{\otimes n}}=Q^{\otimes n}.$$
--   Zero-$P$ entries carry no moment mass and $Q$ need not normalize. This transfers the finite-likelihood quantum moments to a classical iid model.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 14, §V-A Eq. (16): NS moment and tensor identities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Eq.(16), PDF p.14, and centered interpretation p.19. Tensor identities use
product eigenbases; no assertion of basis-independent arrays in degenerate spaces. Source correction. Printed: Definition 1 p.7 calls the raw second moment V; Eq.(16) matches the first two likelihood moments.
Changed: State the centered variance identity, subtracting D^2 on both sides.
Why: The first moments also agree, so centering both second moments gives precisely the variance used in Section VI p.19. -/
theorem ns_moments_tensor (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (hsupport : SupportIncluded rho sigma)
    (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma) :
    classicalMean (nsProbability r s) (nsReferenceWeight r s) = relativeMean rho sigma ∧
    classicalVariance (nsProbability r s) (nsReferenceWeight r s) = centeredRelativeVariance rho sigma ∧
    (∀ n, nsTensorP r s n = weightPower n (nsProbability r s)) ∧
    (∀ n, nsTensorQ r s n = weightPower n (nsReferenceWeight r s)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
