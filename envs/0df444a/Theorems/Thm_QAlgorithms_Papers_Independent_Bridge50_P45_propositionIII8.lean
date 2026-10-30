-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionIII8
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionIII8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:16:36.396109+00:00
-- url     : https://prove2.me/theorems/67e7217f-d5c7-41f2-a7e3-68a30e3ee0f7
-- title:
--   Gibbs decomposition and corrected normalized divergence identities
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   Assume $P=\rho^0\wedge\sigma^0\ne0$, $\alpha>0$, $\alpha\ne1$, and either $\alpha<1$ or $\rho^0\le\sigma^0$. Let $\tau_\alpha$ be the normalized Gibbs state above. For every density operator $\tau$ supported on $P$,
--   $$\alpha D(\tau\|\rho)+(1-\alpha)D(\tau\|\sigma)=D(\tau\|\tau_\alpha)-\psi^\flat_\alpha(\rho\|\sigma),$$
--   $$D^\flat_\alpha(\rho\|\sigma)=\frac\alpha{1-\alpha}D(\tau\|\rho)+D(\tau\|\sigma)-\frac{D(\tau\|\tau_\alpha)}{1-\alpha}-\frac{\log\operatorname{Tr}\rho}{\alpha-1}.$$
--   The state $\tau_\alpha$ uniquely minimizes the weighted entropy on $\mathcal S_P(H)$, its minimum is $-\psi^\flat_\alpha$, and
--   $$D^\flat_\alpha(\rho\|\sigma)=\frac\alpha{1-\alpha}D(\tau_\alpha\|\rho)+D(\tau_\alpha\|\sigma)-\frac{\log\operatorname{Tr}\rho}{\alpha-1}.$$
--
--
--   This refines the state variational formula by its relative-entropy remainder.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 11, Proposition III.8 Let ̺, σ ∈ L(H)+ be such that P := ̺0 ∧ σ 0 6= 0, and let τα be as in (40). For every

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

/-- Proposition III.8, PDF pp.11-12 (46)-(47). SOURCE CORRECTIONS: the finite-Q
support domain is explicit, and each normalized-D identity includes
-log(Tr rho)/(a-1). Without these corrections tau_a need not be a state. -/
theorem propositionIII8 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma)
    (a : ℝ) (ha : 0 < a) (hne : a ≠ 1) (hP : meetSupport rho sigma ≠ 0)
    (hfinite : a < 1 ∨ SupportIncluded rho sigma) :
    let tauA := logEuclideanOptimizer a rho sigma
    (∀ tau ∈ statesOn (meetSupport rho sigma),
      entropyObjective a rho sigma tau = relativeEntropy tau tauA - logTraceFunctional .b a rho sigma ∧
      renyiValue .b a rho sigma = ((a/(1-a) : ℝ) : EReal) * relativeEntropy tau rho +
        relativeEntropy tau sigma - (((1-a)⁻¹ : ℝ) : EReal) * relativeEntropy tau tauA -
        ((Real.log rho.trace.re/(a-1) : ℝ) : EReal)) ∧
    Minimizes (statesOn (meetSupport rho sigma)) (entropyObjective a rho sigma) tauA ∧
    (∀ tau, Minimizes (statesOn (meetSupport rho sigma)) (entropyObjective a rho sigma) tau → tau = tauA) ∧
    logTraceFunctional .b a rho sigma = -entropyObjective a rho sigma tauA ∧
    renyiValue .b a rho sigma = ((a/(1-a) : ℝ) : EReal) * relativeEntropy tauA rho +
      relativeEntropy tauA sigma - ((Real.log rho.trace.re/(a-1) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
