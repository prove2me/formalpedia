-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_square
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:19.519648+00:00
-- url     : https://prove2.me/theorems/cfb8e9b6-41c2-48bc-b088-84a24059021a
-- title:
--   Decoder Dressed Logical: phase Operator square
-- statement:
--   Every decoder phase operator squares to the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L362-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L362-L366

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_square
    (D : DecoderDressedLogical H) (logical : Binary ι) :
    D.phaseOperator logical * D.phaseOperator logical = 1 := by sorry
