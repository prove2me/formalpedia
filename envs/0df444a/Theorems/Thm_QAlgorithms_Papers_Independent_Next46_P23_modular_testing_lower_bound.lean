-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_modular_testing_lower_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P23.modular_testing_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:47:00.628992+00:00
-- url     : https://prove2.me/theorems/c610a9f4-5154-43bd-a2a2-2e668ddb325b
-- title:
--   Proposition 2.26
-- statement:
--   Let $\rho,\nu$ be arbitrary normalized states on a nonzero finite-dimensional complex Hilbert space and let $0<p<1$ be the prior of $\rho$. Let $D_p$ be the minimum Bayesian error over all orthogonal projection tests, with outcome one accepting $\rho$. Let $\mu_{\rho\mid\nu}$ be the spectral measure of the nonnegative relative modular operator $\Delta_{\rho\mid\nu}$ in $\sqrt\nu$, using the support inverse when $\nu$ is singular. Then $$D_p(\rho,\nu)\ge\frac12\min(p,1-p)\mu_{\rho\mid\nu}([1,\infty)).$$ The threshold is on the operator itself, without logarithm or time rescaling.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 69, Proposition 2.26

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition2.26, source PDF p.69; singular states use the generalized inverse of p.67.
The threshold applies to Delta itself. The prior obeys 0<p<1. -/
theorem modular_testing_lower_bound [Nonempty I] (rho nu : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hnu : QAlgorithms.IsDensityMatrix nu)
    (p : ℝ) (hp : 0 < p) (hpone : p < 1) :
    (1/2 : ℝ) * min p (1-p) * ((relativeModularMeasure rho nu) (Set.Ici 1)).toReal ≤
      optimalTestingError p rho nu := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
