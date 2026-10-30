-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII19
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:21:48.024044+00:00
-- url     : https://prove2.me/theorems/bf3d97de-d846-4c26-ae19-bb9cf457305e
-- title:
--   Tensor-power additivity and scaling
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For positive finite $\alpha\ne1$, every $n\in\mathbb N$, and every $\lambda>0$,
--   $$Q^t_\alpha(\rho^{\otimes n}\|\sigma^{\otimes n})=Q^t_\alpha(\rho\|\sigma)^n,$$
--   $$Q^t_\alpha(\lambda\rho\|\sigma)=\lambda^\alpha Q^t_\alpha(\rho\|\sigma),\qquad
--   Q^t_\alpha(\rho\|\lambda\sigma)=\lambda^{1-\alpha}Q^t_\alpha(\rho\|\sigma).$$
--   For every $\alpha\in(0,\infty]\setminus\{1\}$ the corresponding divergence identities are
--   $$D^t_\alpha(\rho^{\otimes n}\|\sigma^{\otimes n})=nD^t_\alpha(\rho\|\sigma),$$
--   $$D^t_\alpha(\lambda\rho\|\sigma)=D^t_\alpha(\rho\|\sigma)+\log\lambda,\qquad
--   D^t_\alpha(\rho\|\lambda\sigma)=D^t_\alpha(\rho\|\sigma)-\log\lambda.$$
--   At $n=0$ the tensor unit has divergence zero and $0\cdot(\pm\infty)=0$.
--
--   The Q identities are restricted to finite order, while divergence additivity and scaling include infinity.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 16, Lemma III.19 Let ̺, σ ∈ L(H)+ , α ∈ (0, +∞] \ {1}, and t be any of the three possible values.

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

/-- Lemma III.19, PDF p.16 (67). Q claims have finite order; D includes infinity.
At n=0 extended multiplication uses 0 times infinity = 0, the scalar tensor unit. -/
theorem lemmaIII19 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (t : Flavor) :
    (∀ a : ℝ, 0 < a → a ≠ 1 →
      (∀ n : ℕ, regularizedTrace t a (copies n rho) (copies n sigma) = regularizedTrace t a rho sigma ^ n) ∧
      (∀ l : ℝ, 0 < l →
        regularizedTrace t a ((l : ℂ) • rho) sigma = ((Real.rpow l a : ℝ) : EReal) * regularizedTrace t a rho sigma ∧
        regularizedTrace t a rho ((l : ℂ) • sigma) = ((Real.rpow l (1-a) : ℝ) : EReal) * regularizedTrace t a rho sigma)) ∧
    (∀ a : EReal, 0 < a → a ≠ 1 →
      (∀ n : ℕ, renyiValue t a (copies n rho) (copies n sigma) = (n : EReal) * renyiValue t a rho sigma) ∧
      (∀ l : ℝ, 0 < l →
        renyiValue t a ((l : ℂ) • rho) sigma = renyiValue t a rho sigma + (Real.log l : EReal) ∧
        renyiValue t a rho ((l : ℂ) • sigma) = renyiValue t a rho sigma - (Real.log l : EReal))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
