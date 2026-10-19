-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unitalStabilizable_criteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unitalStabilizable_criteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:34:07.358406+00:00
-- url     : https://prove2.me/theorems/d7b51828-a030-4bf7-9bde-dcda06dcc4d8
-- title:
--   Corollary 5.7: Unital stabilizable systems
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, the following are equivalent: unitality together with stabilization of every simplex point; simultaneous special-unitary diagonalization of the jumps; normality and pairwise commutation of the jumps; and
--
--   $$J(U)\text{ diagonal for some }U\in SU(n)\quad\Longleftrightarrow\quad L_U=0\text{ for some }U\in SU(n).$$
--
--   The two jump-family conditions may each be imposed on some or, equivalently, every representation. These are the unital stabilizable systems.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 25, Corollary 5.7: Unital stabilizable systems

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

/-- arXiv:2308.00561v1, PDF p.25, Corollary 5.7: Unital stabilizable systems. Both normality and commutation are present. A single arbitrary jump is triangularizable but need not be normal. -/
theorem unitalStabilizable_criteria {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    List.TFAE [unital D ∧ stabilizableSystem D,
      someRepresentation D diagonalizableJumps,
      everyRepresentation D diagonalizableJumps,
      someRepresentation D normalCommutingJumps,
      everyRepresentation D normalCommutingJumps,
      (∃ U, specialUnitary U ∧ ∀ i j, i ≠ j → rates D.jump U i j = 0),
      (∃ U, specialUnitary U ∧ populationGenerator D.jump U = 0)] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
