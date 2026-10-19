-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_triangularization_iffUnitary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.triangularization_iffUnitary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:48:18.14998+00:00
-- url     : https://prove2.me/theorems/230e70f5-cd9a-49e2-904c-d452ac839f05
-- title:
--   Footnote 8: unitary triangularization
-- statement:
--   For any family $\mathcal A\subseteq M_n(\mathbb C)$, $n\ge2$,
--
--   $$\mathcal A\text{ simultaneously triangularizable}\quad\Longleftrightarrow\quad\exists U\in U(n):U^*AU\text{ upper triangular for every }A\in\mathcal A.$$
--
--   The same unitary works for the whole family. This is a simultaneous flag statement, not a choice of a different Schur basis for each matrix.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 12, Footnote 8: unitary triangularization

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

/-- arXiv:2308.00561v1, PDF p.12, Footnote 8: unitary triangularization.  -/
theorem triangularization_iffUnitary {n : ℕ} (hn : 2 ≤ n) (A : Set (Mat n)) :
    triangularizable A ↔ unitarilyTriangularizable A := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
