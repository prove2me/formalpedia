-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIII17
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIII17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:19:51.052068+00:00
-- url     : https://prove2.me/theorems/e26b8ef0-004e-4b65-9cce-6f7ca797c217
-- title:
--   Pinching counterexamples for the log-Euclidean functional
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For every $\alpha>1$ there exist nonzero positive semidefinite $2\times2$ matrices $\rho,\sigma$ such that, with $\mathcal E_\sigma(A)=\sum_sP_sAP_s$ the pinching by the distinct spectral projections of $\sigma$,
--   $$Q^\flat_\alpha(\rho\|\sigma)<Q^\flat_\alpha(\mathcal E_\sigma(\rho)\|\sigma).$$
--   Consequently $D^\flat_\alpha$ fails data processing under CPTP maps and $Q^\flat_\alpha$ is not jointly convex.
--
--   The witness is chosen after the order, and two dimensions avoid a vacuous one-dimensional counterexample.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 15, Lemma III.17 Q♭α is not monotone under CPTP maps for any α > 1. In fact, it is not even monotone

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

/-- Lemma III.17, PDF p.15: a two-dimensional pinching witness after each order,
nonmonotonicity under CPTP maps, and failure of joint convexity. -/
theorem lemmaIII17 (a : ℝ) (ha : 1 < a) :
    (∃ rho sigma : Mat (Fin 2), NonzeroPSD rho ∧ NonzeroPSD sigma ∧
      regularizedTrace .b a rho sigma < regularizedTrace .b a (pinch sigma rho) sigma) ∧
    ¬ DataProcessing .b a ∧ ¬ JointConvexQ .b a := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
