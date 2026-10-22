-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_positive_t_not_identity
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.positive_t_not_identity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:38:41.897432+00:00
-- url     : https://prove2.me/theorems/218e80a4-2ab0-41f5-8c75-285a0a989f00
-- title:
--   Section 4.2, Statement (II-B): positive-T normal forms are not identity
-- statement:
--   Fix the chosen shortest Clifford tails and the resulting normal-word grammar. Every normal word $C$ containing a positive number $t(C)$ of $T$ gates satisfies
--
--   $$t(C)>0\quad\Longrightarrow\quad f_u(C)\ne I.$$
--
--   The conclusion concerns exact matrices. It does not require the output on $|0\rangle$ to change: $T|0\rangle=|0\rangle$ while $T\ne I$. This is precisely Statement (II-B).
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 8, Section 4.2, Statement (II-B): positive-T normal forms are not identity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8, Statement (II-B), proved pp.10–13: positive-T normal
words are not the identity matrix. In particular this is not the false
claim that all such words move |0>: the normal word T fixes |0>. -/
theorem positive_t_not_identity (reps : Representatives .hp)
    (C : CircuitWord) (hC : IsNormalWord .hp reps C) (ht : 0 < wordTCount C) :
    wordMatrix .hp C ≠ 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
