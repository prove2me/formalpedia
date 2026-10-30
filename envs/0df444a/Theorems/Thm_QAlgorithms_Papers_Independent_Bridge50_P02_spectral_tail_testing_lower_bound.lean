-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_spectral_tail_testing_lower_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.spectral_tail_testing_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:43:29.118978+00:00
-- url     : https://prove2.me/theorems/09f108d5-de48-4100-b276-d7866c4c4f16
-- title:
--   Corollary 2: spectral-tail lower bound for testing
-- statement:
--   Let $\rho,\sigma$ be arbitrary strictly positive operators on a nonzero finite-dimensional complex Hilbert space, and let $\nu,\theta\in\mathbb R$. Define $e^*_{\rm sym}$ as the optimal sum of the two errors over all effects. Let $\mu_{\sigma\mid\rho}$ be the spectral measure of $-\log\Delta_{\sigma\mid\rho}$ in $\Omega_\rho=\sqrt\rho$, of mass $\operatorname{Tr}\rho$. Then
--   $$e^*_{\rm sym}(\sigma,e^{-\theta}\rho)\ge\frac{e^{-\theta}}{1+e^{\nu-\theta}}\,\mu_{\sigma\mid\rho}(({-\infty},\nu]).$$
--
--   This one-shot bound controls testing error using a spectral lower tail. The right side uses finite mass, becoming a probability expression when $\operatorname{Tr}\rho=1$.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 13, Corollary 2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Corollary 2, PDF p.13, (3.13): denominator 1+exp(nu-theta), finite tail mass
of mu_(sigma|rho), with total mass Tr rho. -/
theorem spectral_tail_testing_lower_bound [Nonempty I] (rho sigma : Mat I)
    (hrho : rho.PosDef) (hsigma : sigma.PosDef) (nu theta : ℝ) :
    Real.exp (-theta) / (1+Real.exp (nu-theta)) * spectralTail sigma rho nu ≤
      symmetricError sigma ((Real.exp (-theta) : ℂ) • rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
