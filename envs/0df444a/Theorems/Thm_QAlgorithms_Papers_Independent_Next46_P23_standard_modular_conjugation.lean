-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_standard_modular_conjugation
-- name    : QAlgorithms.Papers.Independent.Next46.P23.standard_modular_conjugation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:45:38.20371+00:00
-- url     : https://prove2.me/theorems/183adfa3-4c19-4b9e-9c96-f53dde95be37
-- title:
--   Proposition 2.24
-- statement:
--   On Hilbert–Schmidt matrices over a nonzero finite-dimensional complex Hilbert space, $J\xi=\xi^*$ is an anti-unitary involution. Writing $L(A)\xi=A\xi$, $$JL(B(K))J=L(B(K))^\prime.$$ The positive-matrix cone is self-dual for the real nonnegative Hilbert–Schmidt pairing and is fixed pointwise by $J$. For every element $X$ of the intersection of the left algebra and its commutant, $JXJ=X^*$. Finally $L(A)JL(A)$ preserves this cone for every $A$. These are the six standard-form properties.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 60, Proposition 2.24

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

/-- Proposition2.24, all six natural-cone and modular-conjugation clauses, source PDF p.60. -/
theorem standard_modular_conjugation [Nonempty I] :
    ((∀ xi eta : Mat I, ∀ c : ℂ, (xi+eta)ᴴ = xiᴴ + etaᴴ ∧
      (c • xi)ᴴ = conj c • xiᴴ ∧ (xiᴴ)ᴴ = xi ∧
      (xiᴴ * eta).trace = conj (((xiᴴ)ᴴ * etaᴴ).trace)) ∧
      (∀ xi : Mat I, QAlgorithms.frobNorm (xiᴴ) = QAlgorithms.frobNorm xi)) ∧
    (conjugateByJ '' Set.range (leftMatrix : Mat I → Mat (I × I)) =
      matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I)))) ∧
    (∀ xi : Mat I, xi.PosSemidef ↔
      ∀ eta : Mat I, eta.PosSemidef → (xiᴴ*eta).trace.im = 0 ∧ 0 ≤ (xiᴴ*eta).trace.re) ∧
    (∀ xi : Mat I, xi.PosSemidef → xiᴴ = xi) ∧
    (∀ X : Mat (I × I), X ∈ Set.range (leftMatrix : Mat I → Mat (I × I)) →
      X ∈ matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I))) → conjugateByJ X = Xᴴ) ∧
    (∀ A xi : Mat I, xi.PosSemidef → (A * (A*xi)ᴴ).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
