-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_triangularization_iffSolvable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.triangularization_iffSolvable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:19:46.44243+00:00
-- url     : https://prove2.me/theorems/8f07c0d8-d5ae-473d-83f0-3e7605048e8a
-- title:
--   Lemma 3.12: Triangularizability and solvable Lie algebras
-- statement:
--   For any set $\mathcal A\subseteq\mathbb C^{n\times n}$, $n\ge2$,
--
--   $$\mathcal A\text{ is simultaneously triangularizable}\quad\Longleftrightarrow\quad\operatorname{Lie}_{\mathbb C}(\mathcal A)\text{ is solvable}.$$
--
--   The family may be infinite or empty; no specified Lindblad representation is needed.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 12, Lemma 3.12: Triangularizability and solvable Lie algebras

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

/-- arXiv:2308.00561v1, PDF p.12, Lemma 3.12: Triangularizability and solvable Lie algebras. Quantifies an arbitrary set, not just a finite jump family. The empty family has the zero generated Lie algebra and is triangularizable. -/
theorem triangularization_iffSolvable {n : ℕ} (hn : 2 ≤ n) (A : Set (Mat n)) :
    triangularizable A ↔ solvableGenerated A := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
