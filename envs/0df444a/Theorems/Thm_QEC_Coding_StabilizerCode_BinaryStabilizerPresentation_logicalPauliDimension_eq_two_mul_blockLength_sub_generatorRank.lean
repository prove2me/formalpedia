-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:15.210237+00:00
-- url     : https://prove2.me/theorems/b7441b7c-ac61-4784-9061-e634afdf1da8
-- title:
--   Binary Stabilizer Presentation: logical Pauli Dimension eq two mul block Length sub generator Rank
-- statement:
--   The normalizer quotient has exactly twice the encoded-qubit dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L331-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L331-L342

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.logicalPauliDimension = 2 * (P.blockLength - P.generatorRank) := by sorry
