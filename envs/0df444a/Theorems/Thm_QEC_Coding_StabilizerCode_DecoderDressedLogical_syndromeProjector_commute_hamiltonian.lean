-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_hamiltonian
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:06.194646+00:00
-- url     : https://prove2.me/theorems/0a05ea14-2fcf-44b8-9345-35cfae3fa48e
-- title:
--   Decoder Dressed Logical: syndrome Projector commute hamiltonian
-- statement:
--   The selected Hamiltonian preserves every syndrome sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L326-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L326-L337

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_hamiltonian
    (D : DecoderDressedLogical H) (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) H.operator := by sorry
