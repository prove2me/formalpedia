-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_collision_implies_identity
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.collision_implies_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:37:50.462285+00:00
-- url     : https://prove2.me/theorems/2b207fff-4e21-476e-b42e-cf7b12a59c35
-- title:
--   Section 4.2, Statement (II-A): collision implies a nontrivial identity normal form
-- statement:
--   Fix a shortest Clifford representative system and its normal-word set $\mathcal N$. If distinct normal words have the same exact matrix, then a positive-$T$ normal word computes the identity:
--
--   $$\bigl(\exists C,D\in\mathcal N:\ C\ne D,\ f_u(C)=f_u(D)\bigr)\ \Longrightarrow\ \bigl(\exists E\in\mathcal N:\ t(E)>0,\ f_u(E)=I\bigr).$$
--
--   Here $t$ counts literal $T$ symbols and equality is exact matrix equality. This preserves the full conditional reduction labeled (II-A).
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 8, Section 4.2, Statement (II-A): collision implies a nontrivial identity normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8, Statement (II-A), proved pp.9–10: a collision of distinct
normal words implies a positive-T normal word computing the identity. -/
theorem collision_implies_identity (reps : Representatives .hp) :
    (∃ C D : CircuitWord, IsNormalWord .hp reps C ∧ IsNormalWord .hp reps D ∧
      C ≠ D ∧ wordMatrix .hp C = wordMatrix .hp D) →
    ∃ E : CircuitWord, IsNormalWord .hp reps E ∧ 0 < wordTCount E ∧ wordMatrix .hp E = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
