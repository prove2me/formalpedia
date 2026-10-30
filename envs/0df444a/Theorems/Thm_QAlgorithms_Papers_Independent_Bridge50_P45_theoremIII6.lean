-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_theoremIII6
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.theoremIII6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:15:20.214429+00:00
-- url     : https://prove2.me/theorems/2b28c4fb-310d-4c59-bfd0-f66a89b2702b
-- title:
--   Variational formulas and unique Gibbs optimizers
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   Let $P=\rho^0\wedge\sigma^0$, $\mathcal S_\rho=\{\tau\in\mathcal S(H):\operatorname{supp}\tau\subseteq\operatorname{supp}\rho\}$, and $s(\alpha)=1$ for $\alpha\ge1$ and $-1$ otherwise. Put $c_\alpha(\tau)=\alpha D(\tau\|\rho)+(1-\alpha)D(\tau\|\sigma)$, with $c_1(\tau)=D(\tau\|\rho)$. For $\alpha>0$, $\alpha\ne1$, and $P\ne0$,
--   $$Q^\flat_\alpha=\max_{0\ne\tau\ge0,\,\tau^0\le\rho^0}\{\operatorname{Tr}\tau-c_\alpha(\tau)\},\qquad
--   \psi^\flat_\alpha=-\min_{\tau\in\mathcal S_\rho}c_\alpha(\tau),$$
--   $$D^\flat_\alpha=s(\alpha)\max_{\tau\in\mathcal S_\rho}s(\alpha)\left\{D(\tau\|\sigma)-\frac\alpha{\alpha-1}D(\tau\|\rho)\right\}-\frac{\log\operatorname{Tr}\rho}{\alpha-1}.$$
--   The last two formulas also hold for $P=0$, $0<\alpha<1$; the first two hold at $\alpha=1$ with the zero-coefficient entropy omitted. Every displayed extremum is attained. When $D^\flat_\alpha$ is finite and $\alpha\ne1$, the state
--   $$\tau_\alpha=\frac{P\exp(\alpha P\widehat{\log}\rho P+(1-\alpha)P\widehat{\log}\sigma P)}{Q^\flat_\alpha(\rho\|\sigma)}$$
--   is the unique optimizer of the state extrema, and $Q^\flat_\alpha\tau_\alpha$ attains the positive-operator maximum.
--
--   These variational descriptions connect the log-Euclidean divergence to entropy optimization.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 10, Theorem III.6 For every ̺, σ ∈ L(H)+ such that P := ̺0 ∧ σ 0 6= 0, and for every α ∈ (0, +∞) \ {1},

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

/-- Theorem III.6, PDF pp.10-11 (37)-(40). SOURCE CORRECTION: (39) lacks
-log(Tr rho)/(a-1); it is included here as forced by (26). Order one omits the
zero-coefficient term. All extrema are attained, and finite-order optimizers are unique. -/
theorem theoremIII6 (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma) :
    (∀ a : ℝ, 0 < a → (meetSupport rho sigma ≠ 0 ∨ a = 1) →
      ∃ tau : Mat I,
        AttainsMaximum {tau | NonzeroPSD tau ∧ SupportIncluded tau rho}
          (fun tau => (tau.trace.re : EReal) - entropyObjective a rho sigma tau) tau ∧
        regularizedTrace .b a rho sigma = (tau.trace.re : EReal) - entropyObjective a rho sigma tau) ∧
    (∀ a : ℝ, 0 < a → (meetSupport rho sigma ≠ 0 ∨ a ≤ 1) →
      ∃ tau : Mat I, Minimizes (statesOn rho) (entropyObjective a rho sigma) tau ∧
        logTraceFunctional .b a rho sigma = -entropyObjective a rho sigma tau) ∧
    (∀ a : ℝ, 0 < a → a ≠ 1 → (meetSupport rho sigma ≠ 0 ∨ a < 1) →
      ∃ tau : Mat I, AttainsMaximum (statesOn rho) (dualObjective a rho sigma) tau ∧
        renyiValue .b a rho sigma = (renyiSign a : EReal) * dualObjective a rho sigma tau -
          ((Real.log rho.trace.re/(a-1) : ℝ) : EReal)) ∧
    (∀ a : ℝ, 0 < a → a ≠ 1 → renyiValue .b a rho sigma ≠ ⊤ →
      renyiValue .b a rho sigma ≠ ⊥ →
      let tau := logEuclideanOptimizer a rho sigma
      Minimizes (statesOn rho) (entropyObjective a rho sigma) tau ∧
      (∀ u, Minimizes (statesOn rho) (entropyObjective a rho sigma) u → u = tau) ∧
      AttainsMaximum (statesOn rho) (dualObjective a rho sigma) tau ∧
      (∀ u, AttainsMaximum (statesOn rho) (dualObjective a rho sigma) u → u = tau) ∧
      AttainsMaximum {u | NonzeroPSD u ∧ SupportIncluded u rho}
        (fun u => (u.trace.re : EReal) - entropyObjective a rho sigma u)
        (((regularizedTrace .b a rho sigma).toReal : ℂ) • tau)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
