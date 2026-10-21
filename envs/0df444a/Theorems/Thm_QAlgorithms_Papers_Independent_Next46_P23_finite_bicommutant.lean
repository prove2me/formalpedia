-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_finite_bicommutant
-- name    : QAlgorithms.Papers.Independent.Next46.P23.finite_bicommutant
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:02:27.46488+00:00
-- url     : https://prove2.me/theorems/49e60708-df2a-4e38-9429-cd85ad0e7eac
-- title:
--   Theorem 6.5
-- statement:
--   Let $K$ be finite-dimensional and let $S\subset B(K)$ contain the identity and be closed under adjoints. Then $$S^{\prime\prime}=\operatorname{alg}^*(S),$$ where the right side is the smallest unital complex star-subalgebra containing $S$ and the commutants are taken in all of $B(K)$. This is the finite-dimensional bicommutant theorem; no weak closure is substituted for the algebra.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 122, Theorem 6.5

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

/-- Theorem6.5, finite-dimensional bicommutant theorem, source PDF pp.122--123.
The generated algebra is unital, matching the explicit assumption 1 in S. -/
theorem finite_bicommutant (S : Set (Mat I)) (hunital : 1 ∈ S)
    (hstar : ∀ A ∈ S, Aᴴ ∈ S) :
    matrixCommutant (matrixCommutant S) = (StarAlgebra.adjoin ℂ S : Set (Mat I)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
