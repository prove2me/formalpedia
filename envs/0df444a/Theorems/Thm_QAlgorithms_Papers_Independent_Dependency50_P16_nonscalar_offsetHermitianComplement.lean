-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_nonscalar_offsetHermitianComplement
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.nonscalar_offsetHermitianComplement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:45:36.913978+00:00
-- url     : https://prove2.me/theorems/2f0f4818-0d58-4e14-8fbb-ea21c51b24df
-- title:
--   Corollary C.18: Hermitian complement with a fixed offset
-- statement:
--   For arbitrary $A,C\in M_n(\mathbb C)$, $n\ge2$, with $A$ nonscalar,
--
--   $$\exists B=B^*:\quad\operatorname{alg}_{\mathbb C}(I,A,B+C)=M_n(\mathbb C).$$
--
--   The offset $C$ need not be Hermitian. The Hermitian $B$ is selected after both $A$ and $C$, and the full-algebra equality is retained.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 35, Corollary C.18: Hermitian complement with a fixed offset

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.35, Corollary C.18: Hermitian complement with a fixed offset.  -/
theorem nonscalar_offsetHermitianComplement {n : ℕ} (hn : 2 ≤ n) (A C : Mat n)
    (hA : ¬∃ c : ℂ, A = c • (1 : Mat n)) :
    ∃ B : Mat n, B.IsHermitian ∧ Algebra.adjoin ℂ ({A, B + C} : Set (Mat n)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
