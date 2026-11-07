-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_commute_hamiltonian
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:36:59.953817+00:00
-- url     : https://prove2.me/theorems/7086e8f1-b6f1-46e9-be25-6e35f6ae7664
-- title:
--   Decoder Dressed Logical: dressed Z commute hamiltonian
-- statement:
--   The dressed logical `Z_ec` commutes with the selected Hamiltonian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L655-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L655-L657

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_commute_hamiltonian (D : DecoderDressedLogical H) :
    Commute D.dressedZ H.operator := by sorry
