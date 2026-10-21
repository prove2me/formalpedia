-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_relative_hamiltonian_cocycle
-- name    : QAlgorithms.Papers.Independent.Next46.P23.relative_hamiltonian_cocycle
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:47:49.328219+00:00
-- url     : https://prove2.me/theorems/b9d42bee-b6d5-4ea1-b620-77c591e7bf74
-- title:
--   Proposition 3.1
-- statement:
--   Let $H=H^*$ and let $\omega>0$ be a normalized state on a nonzero finite-dimensional complex Hilbert space. Put $\omega_t=e^{-itH}\omega e^{itH}$ and $\ell_t=\log\omega_t-\log\omega$. For every real $t,s$, $$\ell_{t+s}=\ell_t+\tau^{-t}(\ell_s).$$ For every reversal $\Theta$ of this dynamics and state, $\Theta(\ell_t)=-\tau^t(\ell_t)$. Only the second assertion requires TRI.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 71, Proposition 3.1

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

/-- Proposition3.1, cocycle and conditional reversal for the same Theta; source PDF p.71. -/
theorem relative_hamiltonian_cocycle [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    (∀ t s : ℝ, relativeHamiltonian (evolved H omega (t+s)) omega =
      relativeHamiltonian (evolved H omega t) omega +
        tau H (-t) (relativeHamiltonian (evolved H omega s) omega)) ∧
    (∀ Theta : Reversal I, Reverses Theta H omega → ∀ t : ℝ,
      Theta.map (relativeHamiltonian (evolved H omega t) omega) =
        -tau H t (relativeHamiltonian (evolved H omega t) omega)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
