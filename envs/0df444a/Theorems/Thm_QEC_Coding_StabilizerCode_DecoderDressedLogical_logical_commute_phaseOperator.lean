-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_logical_commute_phaseOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.logical_commute_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:40.674888+00:00
-- url     : https://prove2.me/theorems/687c384e-d4a8-4aa6-9b58-553f0907cffb
-- title:
--   Decoder Dressed Logical: logical commute phase Operator
-- statement:
--   A normalizer logical Pauli commutes with every decoder phase operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L398-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L398-L410

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.logical_commute_phaseOperator
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical)
    (phaseLogical : Binary ι) :
    Commute (toHermitianQubitOperator logical) (D.phaseOperator phaseLogical) := by sorry
