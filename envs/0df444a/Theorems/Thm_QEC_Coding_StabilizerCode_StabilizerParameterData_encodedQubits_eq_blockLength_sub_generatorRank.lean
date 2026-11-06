-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
-- name    : QEC.Coding.StabilizerCode.StabilizerParameterData.encodedQubits_eq_blockLength_sub_generatorRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:47:59.687445+00:00
-- url     : https://prove2.me/theorems/67c01727-5c87-4191-a2ec-c390484748cf
-- title:
--   Stabilizer Parameter Data: encoded Qubits eq block Length sub generator Rank
-- statement:
--   The `[[n,k,d]]` relation follows from the presentation; it is not record data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L394-L397
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L394-L397

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
open QEC.Coding.StabilizerCode.StabilizerParameterData

theorem QEC.Coding.StabilizerCode.StabilizerParameterData.encodedQubits_eq_blockLength_sub_generatorRank
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.encodedQubits = D.blockLength - D.presentation.generatorRank := by sorry
