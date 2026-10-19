-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_nonscalar_hermitianComplement
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.nonscalar_hermitianComplement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:45:05.944193+00:00
-- url     : https://prove2.me/theorems/41496cfd-7ed3-4cb9-b82c-270bdda7ed27
-- title:
--   Lemma C.17: One nonscalar matrix admits a Hermitian algebraic complement
-- statement:
--   Let $A\in M_n(\mathbb C)$, $n\ge2$, be unequal to $cI$ for every $c\in\mathbb C$. Then
--
--   $$\exists B=B^*:\quad\operatorname{alg}_{\mathbb C}(I,A,B)=M_n(\mathbb C).$$
--
--   No normality of $A$ is assumed. The conclusion is equality with the entire associative unital matrix algebra, rather than only a Lie-algebra or irreducibility assertion.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 34, Lemma C.17: One nonscalar matrix admits a Hermitian algebraic complement

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

/-- arXiv:2308.00561v1, PDF p.34, Lemma C.17: One nonscalar matrix admits a Hermitian algebraic complement.  -/
theorem nonscalar_hermitianComplement {n : ℕ} (hn : 2 ≤ n) (A : Mat n)
    (hA : ¬∃ c : ℂ, A = c • (1 : Mat n)) :
    ∃ B : Mat n, B.IsHermitian ∧ Algebra.adjoin ℂ ({A, B} : Set (Mat n)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
