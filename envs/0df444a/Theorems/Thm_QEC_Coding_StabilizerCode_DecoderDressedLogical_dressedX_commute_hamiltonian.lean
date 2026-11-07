-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedX_commute_hamiltonian
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:36:46.503194+00:00
-- url     : https://prove2.me/theorems/1c530e4d-2acf-47da-93a1-6e631cf9b1fd
-- title:
--   Decoder Dressed Logical: dressed X commute hamiltonian
-- statement:
--   The dressed logical `X_ec` commutes with the selected Hamiltonian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L650-L652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L650-L652

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedX_commute_hamiltonian (D : DecoderDressedLogical H) :
    Commute D.dressedX H.operator := by sorry
