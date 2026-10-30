-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:13:25.198266+00:00
-- url     : https://prove2.me/theorems/51b1b728-5d36-4f57-baa0-95a9461a47b7
-- title:
--   Continuity and the support-failure jump of log trace functionals
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For each family $t$, support inclusion implies continuity of $\alpha\mapsto\psi^t_\alpha(\rho\|\sigma)$ on $(0,\infty)$. If support inclusion fails, this map is continuous on $(0,1)$, equals $+\infty$ on $(1,\infty)$, and has an extended left limit satisfying
--   $$\lim_{\alpha\uparrow1}\psi^t_\alpha(\rho\|\sigma)<\log\operatorname{Tr}\rho=\psi^t_1(\rho\|\sigma).$$
--   The left limit may be $-\infty$.
--
--   This identifies the discontinuity responsible for infinite divergence at order one.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 8, Lemma III.3 If ̺0 ≤ σ 0 then ψα (̺kσ) is continuous in α on (0, +∞). If ̺0  σ 0 then ψα (̺kσ) is

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

/-- Lemma III.3, PDF pp.8-9 (29). The left limit is extended-real, including
minus infinity for disjoint supports. -/
theorem lemmaIII3 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (t : Flavor) :
    (SupportIncluded rho sigma → ContinuousOn (fun a => logTraceFunctional t a rho sigma) (Ioi 0)) ∧
    (¬ SupportIncluded rho sigma →
      ContinuousOn (fun a => logTraceFunctional t a rho sigma) (Ioo 0 1) ∧
      (∃ l : EReal, Tendsto (fun a => logTraceFunctional t a rho sigma) (𝓝[<] (1 : ℝ)) (𝓝 l) ∧
        l < (Real.log rho.trace.re : EReal) ∧ logTraceFunctional t 1 rho sigma = (Real.log rho.trace.re : EReal)) ∧
      ∀ a : ℝ, 1 < a → logTraceFunctional t a rho sigma = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
