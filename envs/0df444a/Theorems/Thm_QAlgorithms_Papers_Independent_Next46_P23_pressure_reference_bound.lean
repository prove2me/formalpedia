-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_pressure_reference_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P23.pressure_reference_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:56:47.728083+00:00
-- url     : https://prove2.me/theorems/359f851c-a03b-4001-87d7-433c92b028d6
-- title:
--   Proposition 3.8
-- statement:
--   For self-adjoint $H$ and two faithful normalized reference states $\omega,\rho$ on a nonzero finite-dimensional complex Hilbert space, put $\ell=\log\omega-\log\rho$. For all real $t,\alpha$, $$|e_{\infty,t,\omega}(\alpha)-e_{\infty,t,\rho}(\alpha)|\le(|1-\alpha|+|\alpha|)\|\ell\|.$$ For $t>0$, division by $t$ gives the source’s normalized-pressure estimate. The all-time form avoids the printed division at zero and the negative right side at negative time.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 80, Proposition 3.8

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

/-- Proposition3.8, source PDF p.80. The proof gives the unnormalized all-real-time bound.
The printed divided version requires t>0 (or absolute denominators); t=0 is not divided by. -/
theorem pressure_reference_bound [Nonempty I] (H omega rho : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhofaithful : rho.PosDef) :
    (∀ t a : ℝ, |pressure H omega ⊤ t a - pressure H rho ⊤ t a| ≤
      (|1-a| + |a|) * QAlgorithms.specNorm (relativeHamiltonian omega rho)) ∧
    (∀ t a : ℝ, 0 < t →
      |pressure H omega ⊤ t a / t - pressure H rho ⊤ t a / t| ≤
        (|1-a| + |a|) * QAlgorithms.specNorm (relativeHamiltonian omega rho) / t) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
