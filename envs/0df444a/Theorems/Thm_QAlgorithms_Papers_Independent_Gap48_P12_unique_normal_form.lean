-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_unique_normal_form
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.unique_normal_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:32:50.081492+00:00
-- url     : https://prove2.me/theorems/0fb9f9fe-18e8-4467-aae2-55a0b7a56640
-- title:
--   Theorem 1 (seed paper result): unique exact normal form
-- statement:
--   Fix once and for all one shortest $H/P$ word for each exact Clifford matrix, with ties broken consistently. Let $\mathcal N$ be the normal words of Definition 7: selected Clifford tails, extended recursively by $T$, $HT$, or $PHT$ when the existing word does not start with $T$. For every finite word $C$ over $\{H,P,T\}$, including the empty word, there is exactly one word $D$ such that
--
--   $$D\in\mathcal N,\qquad f_u(D)=f_u(C).$$
--
--   Here $f_u$ is the printed-order product of the one-qubit gate matrices, with empty product $I$. Equality retains global phase, and uniqueness is equality of the complete gate strings. This gives a canonical representative of every exact circuit-equivalence class.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 6, Theorem 1 (seed paper result): unique exact normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.6, Theorem 1 (Definitions 6–7 on p.5): every exact
matrix-equivalence class contains exactly one selected normal-form word. -/
theorem unique_normal_form (reps : Representatives .hp) (C : CircuitWord) :
    ∃! D : CircuitWord, IsNormalWord .hp reps D ∧ wordMatrix .hp D = wordMatrix .hp C := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
