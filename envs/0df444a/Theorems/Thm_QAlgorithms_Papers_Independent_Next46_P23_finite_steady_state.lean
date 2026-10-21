-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_finite_steady_state
-- name    : QAlgorithms.Papers.Independent.Next46.P23.finite_steady_state
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:00:13.911775+00:00
-- url     : https://prove2.me/theorems/bccbc8dc-ea3b-4877-b02a-e5d72326f314
-- title:
--   §5.1: finite-system Cesaro steady state and vanishing fluxes
-- statement:
--   For a nonzero finite-dimensional system with self-adjoint $H$ and faithful normalized $\omega$, let $P_\lambda$ be the spectral projections of $H$. Then $$\omega_+=\sum_\lambda P_\lambda\omega P_\lambda=\lim_{T\to\infty}\frac1T\int_0^T\omega_tdt.$$ The limit is a normalized stationary state; finite dimensionality makes this norm convergence equivalent to convergence of all observable expectations. For every self-adjoint $A$, $\omega_+(i[H,A])=0$. In particular $\omega_+(\sigma)=0$ and $\lim_{t\to\infty}\omega(\Sigma^t)=0$. The separate unbounded confined-system extension is not asserted.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 95, §5.1: finite-system Cesaro steady state and vanishing fluxes

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

/-- Finite-system Cesàro steady state and vanishing fluxes, source PDF p.95, Exercise5.1(1)--(2).
The unbounded infinite-dimensional extension is separately deferred. -/
theorem finite_steady_state [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    QAlgorithms.IsDensityMatrix (steady H omega) ∧
    Tendsto (fun T : ℝ => (T⁻¹ : ℝ) • ∫ t in (0 : ℝ)..T, evolved H omega t)
      atTop (nhds (steady H omega)) ∧
    (∀ t : ℝ, evolved H (steady H omega) t = steady H omega) ∧
    (∀ A : Mat I, A.IsHermitian → ev (steady H omega) (Complex.I • (H*A - A*H)) = 0) ∧
    ev (steady H omega) (entropyProduction H omega) = 0 ∧
    Tendsto (fun t : ℝ => ev omega (averagedProduction H omega t)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
