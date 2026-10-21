-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_compressed_peierls
-- name    : QAlgorithms.Papers.Independent.Next46.P23.compressed_peierls
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:37:26.794981+00:00
-- url     : https://prove2.me/theorems/0a0ec132-6c42-4aa7-b0cd-b1bb166ad037
-- title:
--   Corollary 2.16
-- statement:
--   For a normalized state $\nu$ and self-adjoint $A$ on a nonzero finite-dimensional complex Hilbert space, $$\operatorname{tr}(e^{\log\nu+A})\ge e^{\nu(A)}.$$ The exponential is compressed to the support of a singular $\nu$, and is zero on its kernel. This is the relative-entropy form of the Peierls bound.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 48, Corollary 2.16

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

/-- Corollary2.16, source PDF p.48, valid also for singular normalized nu. -/
theorem compressed_peierls [Nonempty I] (nu A : Mat I) (hnu : QAlgorithms.IsDensityMatrix nu)
    (hA : A.IsHermitian) : Real.exp (ev nu A) ≤ (compressedExp A nu).trace.re := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
