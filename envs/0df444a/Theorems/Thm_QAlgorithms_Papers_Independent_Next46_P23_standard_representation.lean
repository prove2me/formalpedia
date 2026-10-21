-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_standard_representation
-- name    : QAlgorithms.Papers.Independent.Next46.P23.standard_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:44:50.279989+00:00
-- url     : https://prove2.me/theorems/31f11aed-0a5e-4f0f-b933-5315f4781615
-- title:
--   Proposition 2.23
-- statement:
--   On Hilbert–Schmidt matrices over a nonzero finite-dimensional complex Hilbert space, let $L(A)\xi=A\xi$ and $R(A)\xi=\xi A^*$. Both maps are isometric and injective, and their images are unital star-subalgebras. The first is a complex-linear representation; the second represents the conjugate algebra, so $R(cA)=\bar cR(A)$. Moreover, $$L(B(K))\cap R(B(K))=\mathbb CI,\quad L(B(K))\vee R(B(K))=B(H_{B(K)}),\quad L(B(K))^\prime=R(B(K)),\quad R(B(K))^\prime=L(B(K)).$$ The join denotes the generated star-algebra. This retains all six algebra and commutant clauses with the scalar convention made explicit.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 59, Proposition 2.23

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

/-- Proposition2.23, all six clauses, source PDF p.59.
R is a conjugate-algebra representation: scalar c acts by conjugate c. It is not
asserted to be complex-linear with the unchanged scalar action. -/
theorem standard_representation [Nonempty I] :
    ((∀ A : Mat I, QAlgorithms.specNorm (leftMatrix A) = QAlgorithms.specNorm A ∧
      QAlgorithms.specNorm (rightMatrix A) = QAlgorithms.specNorm A) ∧
      Function.Injective (leftMatrix : Mat I → Mat (I × I)) ∧
      Function.Injective (rightMatrix : Mat I → Mat (I × I))) ∧
    (leftMatrix (1 : Mat I) = 1 ∧ rightMatrix (1 : Mat I) = 1 ∧
      ∀ A B : Mat I, ∀ c : ℂ,
      leftMatrix (A+B) = leftMatrix A + leftMatrix B ∧
      rightMatrix (A+B) = rightMatrix A + rightMatrix B ∧
      leftMatrix (c • A) = c • leftMatrix A ∧ rightMatrix (c • A) = conj c • rightMatrix A ∧
      leftMatrix (A*B) = leftMatrix A * leftMatrix B ∧
      rightMatrix (A*B) = rightMatrix A * rightMatrix B ∧
      leftMatrix (Aᴴ) = (leftMatrix A)ᴴ ∧ rightMatrix (Aᴴ) = (rightMatrix A)ᴴ) ∧
    (Set.range (leftMatrix : Mat I → Mat (I × I)) ∩ Set.range (rightMatrix : Mat I → Mat (I × I)) =
      {X | ∃ c : ℂ, X = c • 1}) ∧
    (StarAlgebra.adjoin ℂ (Set.range (leftMatrix : Mat I → Mat (I × I)) ∪
      Set.range (rightMatrix : Mat I → Mat (I × I))) = ⊤) ∧
    (matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I))) = Set.range rightMatrix) ∧
    (matrixCommutant (Set.range (rightMatrix : Mat I → Mat (I × I))) = Set.range leftMatrix) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
