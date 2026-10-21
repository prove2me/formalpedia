-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_renyi_monotonicity
-- name    : QAlgorithms.Papers.Independent.Next46.P23.renyi_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:57:32.539866+00:00
-- url     : https://prove2.me/theorems/f20fbd53-6cb0-4467-99b2-7a4f19f8e44e
-- title:
--   Theorem 2.13
-- statement:
--   Let $\Phi:B(K)\to B(K^\prime)$ be a unital complex-linear Schwarz map, and let $\rho,\nu$ be normalized states on the CODOMAIN algebra $B(K^\prime)$. For $0\le\alpha\le1$, $$S_\alpha(\rho\circ\Phi\mid\nu\circ\Phi)\ge S_\alpha(\rho\mid\nu).$$ Both Hilbert spaces are nonzero and finite-dimensional. Pullbacks are represented by their trace-dual densities; singular states remain allowed.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 46, Theorem 2.13

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

/-- Theorem2.13, states on the codomain of Phi, source PDF p.46. -/
theorem renyi_monotonicity [Nonempty I] [Nonempty J] (Phi : Mat I →ₗ[ℂ] Mat J)
    (hunital : Phi 1 = 1) (hschwarz : Schwarz Phi)
    (rho nu : Mat J) (hrho : QAlgorithms.IsDensityMatrix rho) (hnu : QAlgorithms.IsDensityMatrix nu)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    renyi rho nu a ≤ renyi (pullback Phi rho) (pullback Phi nu) a := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
