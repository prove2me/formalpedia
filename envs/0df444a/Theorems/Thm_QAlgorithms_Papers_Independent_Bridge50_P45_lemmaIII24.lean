-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII24
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII24
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:24:33.689003+00:00
-- url     : https://prove2.me/theorems/f66ec0e5-360a-49b2-a8d5-50cd1c1eae8a
-- title:
--   Loewner monotonicity in the reference argument
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For nonzero positive semidefinite $\sigma'\ge\sigma$,
--   $$D^t_\alpha(\rho\|\sigma')\le D^t_\alpha(\rho\|\sigma)$$
--   holds for the Petz family at $\alpha\in[0,1]$, the sandwiched family at $\alpha\in[1/2,\infty]$, and the log-Euclidean family at $\alpha\in[0,\infty]$.
--
--   The Petz parameter range is exactly the one printed in this lemma.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 17, Lemma III.24 For every ̺ ∈ L(H)+ , we have

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Lemma III.24, PDF p.17: Loewner increase of the reference decreases D,
in precisely the source's parameter ranges. -/
theorem lemmaIII24 (rho sigma sigmaNew : Mat I) (hrho : NonzeroPSD rho)
    (hsigma : NonzeroPSD sigma) (hnew : NonzeroPSD sigmaNew) (horder : (sigmaNew-sigma).PosSemidef)
    (t : Flavor) (a : EReal) (ha : ReferenceRange t a) :
    renyiValue t a rho sigmaNew ≤ renyiValue t a rho sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
