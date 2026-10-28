-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_gibbs_constrained_entropy
-- name    : QAlgorithms.Papers.Independent.Next46.P23.gibbs_constrained_entropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:42:03.495774+00:00
-- url     : https://prove2.me/theorems/38f2665c-f31c-40dc-860d-ba1cb53a72bc
-- title:
--   Theorem 2.21
-- statement:
--   For a self-adjoint Hamiltonian $H$ on a nonzero finite-dimensional complex Hilbert space, every mean energy $E$ between its least and greatest eigenvalues is realized by a Gibbs state $\rho_\beta$, for some $\beta\in[-\infty,\infty]$. At the infinite endpoints use normalized ground/top eigenspace projections. For any such choice, $$\max_{\rho:\rho(H)=E}S(\rho)=S(\rho_\beta),$$ and the maximizing state is uniquely $\rho_\beta$. The inverse temperature itself need not be unique for scalar $H$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 54, Theorem 2.21

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

/-- Theorem2.21, including endpoint temperatures and unique maximizing STATE; PDF pp.53--54. -/
theorem gibbs_constrained_entropy [Nonempty I] (H : Mat I) (hH : H.IsHermitian) :
    (∀ E : ℝ, E ∈ Set.Icc (sInf (↑(eigenvalues H) : Set ℝ))
      (sSup (↑(eigenvalues H) : Set ℝ)) → ∃ beta : EReal, ev (extendedGibbs H beta) H = E) ∧
    (∀ beta : EReal, QAlgorithms.IsDensityMatrix (extendedGibbs H beta) ∧
      ∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      ev rho H = ev (extendedGibbs H beta) H →
        entropy rho ≤ entropy (extendedGibbs H beta) ∧
        (entropy rho = entropy (extendedGibbs H beta) ↔ rho = extendedGibbs H beta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
