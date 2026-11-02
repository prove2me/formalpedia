-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_fourWordFamily
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.fourWordFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:43:46.195753+00:00
-- url     : https://prove2.me/theorems/14b62eab-b162-4c07-a210-375e07461d74
-- title:
--   III C: algebraic direct-sum structure of (14)
-- statement:
--   For a tail length $n\ge2$, consider the explicit code of total block length $n+1$
--
--   $$C_{n+1}=\{0^{n+1},\ 0\,1^n,\ 1\,0^n,\ 1^{n+1}\}.$$
--
--   Its four words are distinct, it is closed under bitwise XOR, and
--
--   $$C_{n+1}=|R_1|R_n|,\qquad Q_{C_{n+1}}^*=Q_{R_n}^*.$$
--
--   Here the direct sum is Cartesian concatenation and the thresholds refer to Bob-only postselection of the six-state input. This identifies the algebraic structure and exact threshold of the family containing all three displayed four-word codes in equation (14). It makes no claim that this family is optimal among all four-word codes.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 6, III C: algebraic direct-sum structure of (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.6, (14): the explicit four-word family is linear, equals R1 direct-sum Rn,
and has the Rn threshold; its total block length is n+1≥3. No optimality is claimed. -/
theorem fourWordFamily {n : ℕ} (hn : 2 ≤ n) :
    fourWordCode n = codeProduct (repetition (Fin 1)) (repetition (Fin n)) ∧
    Function.Injective (fourWordCode n) ∧ CodeLinear (fourWordCode n) ∧
    bobThreshold (fourWordCode n) = bobThreshold (repetition (Fin n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
