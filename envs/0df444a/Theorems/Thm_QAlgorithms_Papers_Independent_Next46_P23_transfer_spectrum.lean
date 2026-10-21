-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_transfer_spectrum
-- name    : QAlgorithms.Papers.Independent.Next46.P23.transfer_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:52:19.696526+00:00
-- url     : https://prove2.me/theorems/57543f40-4229-4ad8-a447-8b26f8be63e9
-- title:
--   Theorem 3.5
-- statement:
--   For a nonzero finite-dimensional quantum dynamical system with self-adjoint $H$ and faithful normalized $\omega$, let $L_p$ be the explicitly defined generator of $U_p$ and $K=L_2$ the standard Liouvillean. For every $p\in[1,\infty]$, $$\operatorname{sp}(L_p)=\operatorname{sp}(K)=\{\lambda-\mu:\lambda,\mu\in\operatorname{sp}(H)\}.$$ Spectra are complex operator spectra, with the displayed differences embedded from the real spectrum of $H$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 77, Theorem 3.5

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

/-- Theorem3.5, spectra of all p-generators, source PDF p.77. -/
theorem transfer_spectrum [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    spectrum ℂ (lpGenerator H omega p) = spectrum ℂ (lpGenerator H omega 2) ∧
    spectrum ℂ (lpGenerator H omega 2) =
      {z | ∃ l ∈ eigenvalues H, ∃ m ∈ eigenvalues H, z = ((l-m : ℝ) : ℂ)} := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
