-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:12:37.123437+00:00
-- url     : https://prove2.me/theorems/d8dec5fd-a536-442f-ad72-ef82448df5b6
-- title:
--   Regularized trace functionals and their support formulas
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For $\alpha>0$, $\alpha\ne1$, the two limits
--   $$\lim_{\varepsilon\downarrow0}Q^t_\alpha(\rho+\varepsilon I\|\sigma+\varepsilon I)
--   =\lim_{\varepsilon\downarrow0}Q^t_\alpha(\rho+\varepsilon(I-\rho^0)\|\sigma+\varepsilon(I-\sigma^0))
--   =Q^t_\alpha(\rho\|\sigma)$$
--   exist. If $\alpha<1$ or $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, then the Petz and sandwiched formulas above hold using support-restricted powers, and, with $P=\rho^0\wedge\sigma^0$,
--   $$Q^\flat_\alpha(\rho\|\sigma)=\operatorname{Tr}P\exp\!\left(\alpha P\widehat{\log}\rho P+(1-\alpha)P\widehat{\log}\sigma P\right).$$
--   For every family, $Q^t_1=\operatorname{Tr}\rho$. If $\alpha>1$ and support inclusion fails, $Q^t_\alpha=+\infty$. On invertible pairs the regularized definitions recover the original trace formulas.
--
--   This establishes consistency of both regularizations and the singular-support extension.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 7, Lemma III.1 For every ̺, σ ∈ L(H)+ , and every α ∈ (0, +∞) \ {1}, the limits in (18) and (19) exist

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

/-- Lemma III.1, PDF pp.7-8 (18)-(22), including order one and support failures. -/
theorem lemmaIII1 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (t : Flavor) (a : ℝ) (ha : 0 < a) (hne : a ≠ 1) :
    Tendsto (fun e : ℝ => (rawQ t a (rho + (e : ℂ) • 1) (sigma + (e : ℂ) • 1) : EReal))
      (𝓝[>] 0) (𝓝 (regularizedTrace t a rho sigma)) ∧
    Tendsto (fun e : ℝ => (rawQ t a (rho + (e : ℂ) • (1-support rho))
      (sigma + (e : ℂ) • (1-support sigma)) : EReal)) (𝓝[>] 0) (𝓝 (regularizedTrace t a rho sigma)) ∧
    ((a < 1 ∨ SupportIncluded rho sigma) →
      regularizedTrace .petz a rho sigma = ((supportPower rho a * supportPower sigma (1-a)).trace.re : EReal) ∧
      regularizedTrace .star a rho sigma = ((supportPower (supportPower rho (1/2) * supportPower sigma ((1-a)/a) * supportPower rho (1/2)) a).trace.re : EReal) ∧
      regularizedTrace .b a rho sigma = ((logEuclideanGibbs a rho sigma).trace.re : EReal)) ∧
    regularizedTrace t 1 rho sigma = (rho.trace.re : EReal) ∧
    ((1 < a ∧ ¬ SupportIncluded rho sigma) → regularizedTrace t a rho sigma = ⊤) ∧
    (rho.PosDef → sigma.PosDef → regularizedTrace t a rho sigma = (rawQ t a rho sigma : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
