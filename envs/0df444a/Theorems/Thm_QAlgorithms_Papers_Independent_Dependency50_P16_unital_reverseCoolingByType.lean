-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_reverseCoolingByType
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_reverseCoolingByType
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:35:40.858981+00:00
-- url     : https://prove2.me/theorems/7d94f4b8-19e1-4c34-b8eb-272b0aaef991
-- title:
--   Corollary 5.10: Unital reverse coolability
-- statement:
--   For a unital GKSL generator on $\mathbb C^n$, $n\ge2$,
--
--   $$\text{(R) reverse coolable}\quad\Longleftrightarrow\quad G\text{ not purely Hamiltonian and of type }(1,\ldots,1)\text{ or }(2,1,\ldots,1).$$
--
--   The type is that of the relaxation algebra, and reverse coolability uses the closure of forward reachability from $e_1$. This expands case (ii) of Theorem 5.9 directly.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 26, Corollary 5.10: Unital reverse coolability

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

/-- arXiv:2308.00561v1, PDF p.26, Corollary 5.10: Unital reverse coolability.  -/
theorem unital_reverseCoolingByType {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (hu : unital D)
    (i0 : Fin n) (hi0 : i0.val = 0) :
    reverseCoolable D i0 ↔ ¬purelyHamiltonian D ∧ smallType D := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
