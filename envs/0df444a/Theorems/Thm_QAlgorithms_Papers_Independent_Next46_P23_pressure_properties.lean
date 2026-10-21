-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_pressure_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.pressure_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:50:50.260359+00:00
-- url     : https://prove2.me/theorems/ee525bef-9bbf-4f14-b045-b7a6ae384587
-- title:
--   Proposition 3.3
-- statement:
--   Consider a nonzero finite-dimensional quantum dynamical system with faithful normalized $\omega$. For each real $t,\alpha$, the entropic pressure $e_{p,t}(\alpha)$ is continuous and nonincreasing in $p\in[1,\infty]$. For each $p,t$ it is real analytic and convex in $\alpha$, vanishes at zero and one, is nonpositive between them and nonnegative outside. It obeys $$e_{p,t}(\alpha)=e_{p,-t}(1-\alpha),\quad e^\prime_{p,t}(0)=\omega(\ell_t)=S(\omega\mid\omega_t),\quad e^\prime_{p,t}(1)=\omega_t(\ell_t)=-S(\omega_t\mid\omega),$$ where $\ell_t=\log\omega_t-\log\omega$. The second derivative at zero is the Kubo–Mori variance of $\ell_t$ for $p=\infty$, and its ordinary variance for $p=2$. Under TRI, $e_{p,t}(\alpha)=e_{p,t}(1-\alpha)$. All seven assertions are included.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 74, Proposition 3.3

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

/-- Proposition3.3, all seven assertions, source PDF p.74.
The p-family is nonincreasing. TRI is required only for the final symmetry. -/
theorem pressure_properties [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    (∀ t a : ℝ,
      ContinuousOn (fun p : ℝ≥0∞ => pressure H omega p t a) (Set.Ici 1) ∧
      AntitoneOn (fun p : ℝ≥0∞ => pressure H omega p t a) (Set.Ici 1)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ t : ℝ,
      AnalyticOnNhd ℝ (pressure H omega p t) Set.univ ∧
      ConvexOn ℝ Set.univ (pressure H omega p t) ∧
      pressure H omega p t 0 = 0 ∧ pressure H omega p t 1 = 0 ∧
      (∀ a ∈ Set.Icc (0 : ℝ) 1, pressure H omega p t a ≤ 0) ∧
      (∀ a : ℝ, a ∉ Set.Icc (0 : ℝ) 1 → 0 ≤ pressure H omega p t a)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ t a : ℝ,
      pressure H omega p t a = pressure H omega p (-t) (1-a)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ t : ℝ,
      deriv (pressure H omega p t) 0 = ev omega (relativeHamiltonian (evolved H omega t) omega) ∧
      ((deriv (pressure H omega p t) (0 : ℝ) : ℝ) : EReal) = signedRelativeEntropy omega (evolved H omega t) ∧
      deriv (pressure H omega p t) 1 = ev (evolved H omega t)
        (relativeHamiltonian (evolved H omega t) omega) ∧
      ((deriv (pressure H omega p t) (1 : ℝ) : ℝ) : EReal) = -signedRelativeEntropy (evolved H omega t) omega) ∧
    (∀ t : ℝ, deriv (deriv (pressure H omega ⊤ t)) 0 =
      (kuboMori omega (relativeHamiltonian (evolved H omega t) omega)
        (relativeHamiltonian (evolved H omega t) omega)).re -
          ev omega (relativeHamiltonian (evolved H omega t) omega) ^ 2) ∧
    (∀ t : ℝ, deriv (deriv (pressure H omega 2 t)) 0 =
      ev omega ((relativeHamiltonian (evolved H omega t) omega) ^ 2) -
        ev omega (relativeHamiltonian (evolved H omega t) omega) ^ 2) ∧
    (TRI H omega → ∀ p : ℝ≥0∞, 1 ≤ p → ∀ t a : ℝ,
      pressure H omega p t a = pressure H omega p t (1-a)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
