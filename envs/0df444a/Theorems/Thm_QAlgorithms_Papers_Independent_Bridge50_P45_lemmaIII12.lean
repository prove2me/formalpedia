-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII12
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:17:13.985318+00:00
-- url     : https://prove2.me/theorems/e76329a6-7baa-4b49-b378-f1896aa03734
-- title:
--   Order convexity and monotonicity of all three families
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For every label $t$,
--   $$\alpha\mapsto\psi^t_\alpha(\rho\|\sigma),\quad\alpha\mapsto Q^t_\alpha(\rho\|\sigma)$$
--   are convex on $(0,\infty)$ in the extended epigraph sense, and $\alpha\mapsto D^t_\alpha(\rho\|\sigma)$ is monotone increasing there.
--
--   These order properties control endpoint limits and auxiliary transforms.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 13, Lemma III.12 Let ̺, σ ∈ L(H)+ , and t be any of the three possible values. Then the functions

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

/-- Lemma III.12, PDF p.13 (56)-(57): both convexities and order monotonicity. -/
theorem lemmaIII12 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (t : Flavor) :
    EConvexOn (Ioi 0) (fun a => logTraceFunctional t a rho sigma) ∧
    EConvexOn (Ioi 0) (fun a => regularizedTrace t a rho sigma) ∧
    MonotoneOn (fun a : ℝ => renyiValue t a rho sigma) (Ioi 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
