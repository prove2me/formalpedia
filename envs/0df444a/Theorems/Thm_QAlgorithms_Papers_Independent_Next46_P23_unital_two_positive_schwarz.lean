-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_unital_two_positive_schwarz
-- name    : QAlgorithms.Papers.Independent.Next46.P23.unital_two_positive_schwarz
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:52:30.944716+00:00
-- url     : https://prove2.me/theorems/a0cc846b-68cc-4ef2-85a0-f78b9c2ffb32
-- title:
--   Proposition 2.7
-- statement:
--   Let $\Phi:B(K)\to B(K^\prime)$ be a unital complex-linear 2-positive map between nonzero finite-dimensional Hilbert spaces. Then $$\Phi(A)^*\Phi(A)\le\Phi(A^*A)\quad\text{for every }A.$$ This is the unital version used by the printed proof. The printed statement omits unitality and fails for the scalar map $A\mapsto2A$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 42, Proposition 2.7

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

/-- Corrected Proposition2.7, source PDF p.42: the proof uses Phi(1)=1.
Printed unitality omission is false for Phi(A)=2A, already on the scalar algebra. -/
theorem unital_two_positive_schwarz [Nonempty I] [Nonempty J] (Phi : Mat I →ₗ[ℂ] Mat J)
    (hunital : Phi 1 = 1) (hpositive : RectangularKPositive 2 Phi) : Schwarz Phi := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
