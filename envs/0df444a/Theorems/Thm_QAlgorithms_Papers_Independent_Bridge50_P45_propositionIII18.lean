-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionIII18
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionIII18
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:20:56.703857+00:00
-- url     : https://prove2.me/theorems/f2206f45-1ed9-425c-b0ed-60933cadae10
-- title:
--   Separate convexity in the reference operator
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For fixed $\rho$, the maps
--   $$\sigma\mapsto s(\alpha)Q^t_\alpha(\rho\|\sigma),\quad
--   \sigma\mapsto s(\alpha)\psi^t_\alpha(\rho\|\sigma),\quad
--   \sigma\mapsto D^t_\alpha(\rho\|\sigma)$$
--   are convex on the nonzero positive semidefinite cone for $t=\flat$, $\alpha\in[0,\infty)$; for $t=*$, $\alpha\in[1/2,\infty)$; and for $t=\{\}$, $\alpha\in[0,2]$. Here $s(\alpha)=1$ at and above one and $-1$ below. The reference maps $D^\flat_\infty(\rho\|\cdot)$ and $D^*_\infty(\rho\|\cdot)$ are also convex.
--
--   These are separate, rather than joint, convexity assertions above order one.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 15, Proposition III.18 For every ̺ ∈ L(H)+ , the functions

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

/-- Proposition III.18, PDF pp.15-16: convexity only in the reference argument;
includes Q and psi at one and b/star divergence at infinity. -/
theorem propositionIII18 (rho : Mat I) (hrho : NonzeroPSD rho) :
    (∀ (t : Flavor) (a : ℝ), SeparateRange t a →
      EConvexOn {sigma : Mat I | NonzeroPSD sigma} (fun sigma => (renyiSign a : EReal) * regularizedTrace t a rho sigma) ∧
      EConvexOn {sigma : Mat I | NonzeroPSD sigma} (fun sigma => (renyiSign a : EReal) * logTraceFunctional t a rho sigma) ∧
      EConvexOn {sigma : Mat I | NonzeroPSD sigma} (fun sigma => renyiValue t a rho sigma)) ∧
    EConvexOn {sigma : Mat I | NonzeroPSD sigma} (fun sigma => renyiValue .b ⊤ rho sigma) ∧
    EConvexOn {sigma : Mat I | NonzeroPSD sigma} (fun sigma => renyiValue .star ⊤ rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
