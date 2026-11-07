-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_errorCorrectedObservable_logical
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.errorCorrectedObservable_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:36:25.193772+00:00
-- url     : https://prove2.me/theorems/5308efa2-909f-4fc3-aacd-a2c7ad364f32
-- title:
--   Decoder Dressed Logical: error Corrected Observable logical
-- statement:
--   The phase-resolution formula equals the literal correction transformation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L418-L455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L418-L455

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.errorCorrectedObservable_logical
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.errorCorrectedObservable (toHermitianQubitOperator logical) =
      D.dressedLogical logical := by sorry
