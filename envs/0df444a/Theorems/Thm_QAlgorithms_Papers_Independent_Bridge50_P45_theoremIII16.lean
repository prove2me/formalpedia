-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_theoremIII16
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.theoremIII16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:18:51.274362+00:00
-- url     : https://prove2.me/theorems/c33df90f-d879-405e-bced-e4e6974b42bf
-- title:
--   Maximal joint-convexity and data-processing intervals
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   Joint convexity means convexity in both matrix arguments in every positive finite dimension; data processing means decrease under every finite-dimensional CPTP map. For nonnegative finite order $\alpha$, each of these properties holds exactly in the corresponding range:
--   $$\begin{array}{c|c}t&\text{joint convexity of }s(\alpha)Q^t_\alpha\text{ and data processing of }D^t_\alpha\\\hline
--   \{\}&[0,2]\\ *&[1/2,\infty)\\ \flat&[0,1]\end{array}$$
--   Here $s(\alpha)=1$ at and above one and $-1$ below one, and $Q_0$ denotes the right limit. In addition $D^*_\infty$ satisfies data processing; no trace functional at infinite order is introduced.
--
--   The equivalences retain the maximality assertion, rather than giving only sufficient parameter ranges.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 14, Theorem III.16 The maximal interval of α for which s(α)Qα is jointly convex is

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

/-- Theorem III.16, PDF pp.14-15. The equivalences express maximality, not
just validity on the listed intervals. Q is not defined at infinite order. -/
theorem theoremIII16 (t : Flavor) :
    (∀ a : ℝ, 0 ≤ a →
      (JointConvexQ t a ↔ match t with
        | .petz => a ≤ 2
        | .star => 1/2 ≤ a
        | .b => a ≤ 1)) ∧
    (∀ a : ℝ, 0 ≤ a →
      (DataProcessing t a ↔ match t with
        | .petz => a ≤ 2
        | .star => 1/2 ≤ a
        | .b => a ≤ 1)) ∧
    DataProcessing .star ⊤ := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
