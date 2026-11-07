-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_commute_hamiltonian
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:24.615207+00:00
-- url     : https://prove2.me/theorems/4113980e-3ee7-4231-a1db-6c4eeda203f3
-- title:
--   Decoder Dressed Logical: dressed Logical commute hamiltonian
-- statement:
--   Every dressed normalizer Pauli commutes with the selected Hamiltonian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L634-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L634-L647

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_hamiltonian
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.dressedLogical logical) H.operator := by sorry
