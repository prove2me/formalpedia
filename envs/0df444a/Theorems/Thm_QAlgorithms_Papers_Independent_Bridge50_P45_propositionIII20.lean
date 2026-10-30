-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionIII20
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionIII20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:22:49.68481+00:00
-- url     : https://prove2.me/theorems/9e8c82d9-873d-4e11-ac40-ad15d89095d6
-- title:
--   Comparison chains between the three divergences
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   The endpoint-extended divergences satisfy both chains
--   $$D^*_\alpha(\rho\|\sigma)\le D_\alpha(\rho\|\sigma)\le D^\flat_\alpha(\rho\|\sigma),\qquad0\le\alpha<1,$$
--   $$D^\flat_\alpha(\rho\|\sigma)\le D^*_\alpha(\rho\|\sigma)\le D_\alpha(\rho\|\sigma),\qquad1<\alpha\le+\infty.$$
--
--
--   These inequalities compare the relevant capacities without identifying noncommuting families.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 16, Proposition III.20 For any ̺, σ ∈ L(H)+ , we have

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

/-- Proposition III.20, PDF p.16 (68)-(69), including both endpoint orders. -/
theorem propositionIII20 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma) :
    (∀ a : EReal, 0 ≤ a → a < 1 →
      renyiValue .star a rho sigma ≤ renyiValue .petz a rho sigma ∧
      renyiValue .petz a rho sigma ≤ renyiValue .b a rho sigma) ∧
    (∀ a : EReal, 1 < a →
      renyiValue .b a rho sigma ≤ renyiValue .star a rho sigma ∧
      renyiValue .star a rho sigma ≤ renyiValue .petz a rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
