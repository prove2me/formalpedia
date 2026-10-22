-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_clifford_three_cosets
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.clifford_three_cosets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:36:04.94798+00:00
-- url     : https://prove2.me/theorems/3344f576-bc40-4957-bd05-c74602f2f079
-- title:
--   Fact 1: three Clifford cosets, each of order 64
-- statement:
--   Let $C_1=\langle H,P\rangle$ and $A=C_T(C_1)$, with exact phase-inclusive matrices. For a matrix $S$, write $SA=\{Sa:a\in A\}$. Then
--
--   $$C_1=A\mathbin{\dot\cup}HA\mathbin{\dot\cup}PHA,\qquad |A|=|HA|=|PHA|=64.$$
--
--   Each set is finite and the three sets are pairwise disjoint. The plus signs printed in Fact 1 mean this partition into left cosets. This partition supplies the three choices of left prefix in the rewrite rule.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 7, Fact 1: three Clifford cosets, each of order 64

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.7, Fact 1 and its following sentence: a disjoint union of
three left cosets, each with exactly 64 distinct exact matrices. -/
theorem clifford_three_cosets :
    cliffordSet .hp = ctSet ∪ leftCoset hadamard ∪ leftCoset (phaseS * hadamard) ∧
    Disjoint ctSet (leftCoset hadamard) ∧
    Disjoint ctSet (leftCoset (phaseS * hadamard)) ∧
    Disjoint (leftCoset hadamard) (leftCoset (phaseS * hadamard)) ∧
    ctSet.Finite ∧ ctSet.ncard = 64 ∧
    (leftCoset hadamard).Finite ∧ (leftCoset hadamard).ncard = 64 ∧
    (leftCoset (phaseS * hadamard)).Finite ∧
      (leftCoset (phaseS * hadamard)).ncard = 64 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
