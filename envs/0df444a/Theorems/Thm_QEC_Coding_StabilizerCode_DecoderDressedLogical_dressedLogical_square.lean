-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_square
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:20.682017+00:00
-- url     : https://prove2.me/theorems/5998d1f3-92bf-4072-a59f-cc3fff5d5d23
-- title:
--   Decoder Dressed Logical: dressed Logical square
-- statement:
--   A dressed normalizer Pauli squares to the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L478-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L478-L498

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_square
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    D.dressedLogical logical * D.dressedLogical logical = 1 := by sorry
