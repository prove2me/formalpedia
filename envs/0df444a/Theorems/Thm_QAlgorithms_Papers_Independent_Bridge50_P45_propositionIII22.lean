-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionIII22
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionIII22
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:23:46.398138+00:00
-- url     : https://prove2.me/theorems/0583c8cb-7a0f-4fa0-8f87-27192f33a8b1
-- title:
--   Strict positivity and proportionality characterization
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For every positive finite order $\alpha$ and every label $t$,
--   $$D^t_\alpha(\rho\|\sigma)\ge\log\operatorname{Tr}\rho-\log\operatorname{Tr}\sigma,$$
--   with equality if and only if $\rho=\lambda\sigma$ for some $\lambda>0$. In particular, for density operators,
--   $$D^t_\alpha(\rho\|\sigma)\ge0,\qquad D^t_\alpha(\rho\|\sigma)=0\iff\rho=\sigma.$$
--   Order zero is excluded.
--
--   This distinguishes strict positivity on states from the possibly negative values on unnormalized pairs.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 17, Proposition III.22 For every α > 0, and all three values of t,

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

/-- Proposition III.22, PDF p.17 (70)-(71): strict positivity and equality
characterization for positive finite orders; order zero is excluded. -/
theorem propositionIII22 (t : Flavor) (a : ℝ) (ha : 0 < a)
    (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma) :
    ((Real.log rho.trace.re - Real.log sigma.trace.re : ℝ) : EReal) ≤ renyiValue t a rho sigma ∧
    (renyiValue t a rho sigma = ((Real.log rho.trace.re - Real.log sigma.trace.re : ℝ) : EReal) ↔
      ∃ l : ℝ, 0 < l ∧ rho = (l : ℂ) • sigma) ∧
    (IsDensityMatrix rho → IsDensityMatrix sigma →
      0 ≤ renyiValue t a rho sigma ∧ (renyiValue t a rho sigma = 0 ↔ rho = sigma)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
