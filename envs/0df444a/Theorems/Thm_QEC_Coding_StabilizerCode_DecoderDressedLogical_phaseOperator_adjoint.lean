-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_adjoint
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:29.130845+00:00
-- url     : https://prove2.me/theorems/0700d92b-af83-4b97-803c-4182d5af15f2
-- title:
--   Decoder Dressed Logical: phase Operator adjoint
-- statement:
--   Decoder phase operators are self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L370-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L370-L384

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_adjoint
    (D : DecoderDressedLogical H) (logical : Binary ι) :
    LinearMap.adjoint (D.phaseOperator logical) = D.phaseOperator logical := by sorry
