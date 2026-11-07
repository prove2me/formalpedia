-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_anticommute_dressedZ
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_anticommute_dressedZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:36:41.764678+00:00
-- url     : https://prove2.me/theorems/3085baf7-438e-4236-8090-58d7b3b6f51b
-- title:
--   Decoder Dressed Logical: dressed X anticommute dressed Z
-- statement:
--   The decoder-dressed logical pair retains the bare Pauli anticommutation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L521-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L521-L550

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_anticommute_dressedZ (D : DecoderDressedLogical H) :
    D.dressedX * D.dressedZ = -(D.dressedZ * D.dressedX) := by sorry
