-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:14:15.990487+00:00
-- url     : https://prove2.me/theorems/60b26230-d002-4e6d-b370-bcdeb46970ca
-- title:
--   The order-one limit is normalized Umegaki entropy
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For each family, the punctured two-sided limit exists and
--   $$\lim_{\alpha\to1}D^t_\alpha(\rho\|\sigma)=D^t_1(\rho\|\sigma)=\frac{D(\rho\|\sigma)}{\operatorname{Tr}\rho}.$$
--   The equality includes support-failure infinity.
--
--   This fixes the normalization shared by all three families at order one.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 9, Lemma III.5 For every ̺, σ ∈ L(H)+ , and all three possible values of t,

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

/-- Lemma III.5, PDF pp.9-10 (34): normalized Umegaki limit, with support-failure infinity. -/
theorem lemmaIII5 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (t : Flavor) :
    Tendsto (fun a : ℝ => finiteD t a rho sigma) (𝓝[≠] 1)
      (𝓝 ((((rho.trace.re)⁻¹ : ℝ) : EReal) * relativeEntropy rho sigma)) ∧
    renyiValue t 1 rho sigma = (((rho.trace.re)⁻¹ : ℝ) : EReal) * relativeEntropy rho sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
