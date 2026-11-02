-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_twoWordClassification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.twoWordClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:40:32.483759+00:00
-- url     : https://prove2.me/theorems/263a0d0a-4fc8-4247-8405-22e78d05beee
-- title:
--   II B / III C: unique two-word code without constant columns
-- statement:
--   Let $n\ge1$ and let $C=\{u,v\}$ consist of two distinct binary words. Put $d=|u\oplus v|$, their Hamming distance, so $d\ge1$. Write $R_j=\{0^j,1^j\}$ for the repetition code, and $Q_C^*$ for the Bob-only symmetric-extendability threshold of its constructed filtered family. Deleting constant coordinates produces a code equivalent to $R_d$, and
--
--   $$Q_C^*=Q_{R_d}^*\le Q_{R_n}^*.$$
--
--   If $C$ already has no constant columns, it is equivalent to $R_n$ and its threshold equals $Q_{R_n}^*$. Thus repetition codes are optimal among two-word codes at the same block length, including the valid one-bit case. This statement does not assert optimality among codes of other sizes.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 6, II B / III C: unique two-word code without constant columns

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF pp.4,6: classification and optimality among two-word codes, including
n=1 and reduction to positive Hamming distance after constant-column deletion. -/
theorem twoWordClassification {n : ℕ} (hn : 1 ≤ n)
    (C : Bool → Qubits n) (hC : Function.Injective C) :
    (NoConstantColumns C → CodeEquivalent C (repetition (Fin n)) ∧
      bobThreshold C = bobThreshold (repetition (Fin n))) ∧
    1 ≤ hammingDist (C false) (C true) ∧
    CodeEquivalent (deleteConstants C)
      (repetition (Fin (hammingDist (C false) (C true)))) ∧
    bobThreshold C = bobThreshold (repetition (Fin (hammingDist (C false) (C true)))) ∧
    bobThreshold C ≤ bobThreshold (repetition (Fin n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
