-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stabilization_algebraicCriteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stabilization_algebraicCriteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:17:22.785917+00:00
-- url     : https://prove2.me/theorems/b50b68f1-6401-4a75-874f-d74709509a5d
-- title:
--   Theorem 3.8: Algebraic characterization of stabilizable systems
-- statement:
--   For a GKSL generator $G$ on $\mathbb C^n$, $n\ge2$, the following are equivalent:
--
--   $$\Delta^{n-1}=\operatorname{stab}_R\quad\Longleftrightarrow\quad\{V_k\}\text{ is simultaneously triangularizable}\quad\Longleftrightarrow\quad\operatorname{Lie}_{\mathbb C}\{V_k\}\text{ is solvable}.$$
--
--   Each jump condition holds for some representation if and only if it holds for every representation of the same generator. In particular, pairwise commuting jumps imply system stabilizability, including a single jump. This characterizes stabilization without imposing normality.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 10, Theorem 3.8: Algebraic characterization of stabilizable systems

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

/-- arXiv:2308.00561v1, PDF p.10, Theorem 3.8: Algebraic characterization of stabilizable systems. Every representation means equality of the actual GKSL operators, with arbitrary finite jump counts. Triangularizability does not mean diagonalizability. -/
theorem stabilization_algebraicCriteria {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    List.TFAE [stabilizableSystem D,
      someRepresentation D (fun E => triangularizable (Set.range E.jump)),
      everyRepresentation D (fun E => triangularizable (Set.range E.jump)),
      someRepresentation D (fun E => solvableGenerated (Set.range E.jump)),
      everyRepresentation D (fun E => solvableGenerated (Set.range E.jump))] ∧
    ((∀ j k, D.jump j * D.jump k = D.jump k * D.jump j) → stabilizableSystem D) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
