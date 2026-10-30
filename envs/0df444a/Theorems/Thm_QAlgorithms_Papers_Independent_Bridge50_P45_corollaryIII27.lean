-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_corollaryIII27
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.corollaryIII27
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:25:23.599816+00:00
-- url     : https://prove2.me/theorems/b1477e8b-6823-485e-b909-538526cfad59
-- title:
--   Lower and upper semicontinuity of trace functionals and divergences
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   Put $A^{\{\}}=A^*=(0,\infty)\setminus\{1\}$ and $A^\flat=(1,\infty)$. For $\alpha\in A^t$ and fixed $\rho$, each of
--   $$\sigma\mapsto s(\alpha)Q^t_\alpha(\rho\|\sigma),\quad
--   \sigma\mapsto s(\alpha)\psi^t_\alpha(\rho\|\sigma),\quad
--   \sigma\mapsto D^t_\alpha(\rho\|\sigma),\quad
--   \sigma\mapsto D^t_\infty(\rho\|\sigma)$$
--   is lower semicontinuous on nonzero PSD references. For positive definite $\sigma$, the maps in the first argument $Q^t_\alpha(\cdot\|\sigma)$, $\psi^t_\alpha(\cdot\|\sigma)$, and $s(\alpha)D^t_\alpha(\cdot\|\sigma)$ are upper semicontinuous on the nonzero PSD cone. These upper semicontinuity assertions also hold for $t=\flat$, $0<\alpha<1$.
--
--   The continuous trace normalization preserves these conclusions without importing the false normalized-D infimum clauses of III.26.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 19, Corollary III.27 Let t be any of the three possible values, and let α ∈ A(t) , where A(t) is given in

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

/-- Corollary III.27, PDF p.19. Semicontinuity follows with continuous trace
normalization; no erroneous infimum formula from III.26 is assumed. -/
theorem corollaryIII27 (t : Flavor) (a : ℝ) (ha : RegularRange t a) :
    (∀ rho : Mat I, NonzeroPSD rho →
      LowerSemicontinuousOn (fun sigma => (renyiSign a : EReal) * regularizedTrace t a rho sigma) {sigma | NonzeroPSD sigma} ∧
      LowerSemicontinuousOn (fun sigma => (renyiSign a : EReal) * logTraceFunctional t a rho sigma) {sigma | NonzeroPSD sigma} ∧
      LowerSemicontinuousOn (fun sigma => renyiValue t a rho sigma) {sigma | NonzeroPSD sigma} ∧
      LowerSemicontinuousOn (fun sigma => renyiValue t ⊤ rho sigma) {sigma | NonzeroPSD sigma}) ∧
    (∀ sigma : Mat I, sigma.PosDef →
      UpperSemicontinuousOn (fun rho => regularizedTrace t a rho sigma) {rho | NonzeroPSD rho} ∧
      UpperSemicontinuousOn (fun rho => logTraceFunctional t a rho sigma) {rho | NonzeroPSD rho} ∧
      UpperSemicontinuousOn (fun rho => (renyiSign a : EReal) * renyiValue t a rho sigma) {rho | NonzeroPSD rho}) ∧
    (∀ b : ℝ, 0 < b → b < 1 → ∀ sigma : Mat I, sigma.PosDef →
      UpperSemicontinuousOn (fun rho => regularizedTrace .b b rho sigma) {rho | NonzeroPSD rho} ∧
      UpperSemicontinuousOn (fun rho => logTraceFunctional .b b rho sigma) {rho | NonzeroPSD rho} ∧
      UpperSemicontinuousOn (fun rho => (renyiSign b : EReal) * renyiValue .b b rho sigma) {rho | NonzeroPSD rho}) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
