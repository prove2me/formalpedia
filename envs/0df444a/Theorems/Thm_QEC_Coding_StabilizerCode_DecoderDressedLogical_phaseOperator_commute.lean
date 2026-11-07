-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_commute
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:03.616247+00:00
-- url     : https://prove2.me/theorems/192b1dda-03a9-44e2-99f5-92b2cc97e83b
-- title:
--   Decoder Dressed Logical: phase Operator commute
-- statement:
--   Any two decoder phase operators commute because they share the resolution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L387-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L387-L395

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_commute
    (D : DecoderDressedLogical H) (left right : Binary ι) :
    Commute (D.phaseOperator left) (D.phaseOperator right) := by sorry
