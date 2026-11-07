-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_hamiltonian
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:17.704713+00:00
-- url     : https://prove2.me/theorems/b77993b8-27aa-404c-a97a-b2f26a8c176f
-- title:
--   Decoder Dressed Logical: good Syndrome Projector commute hamiltonian
-- statement:
--   The good projector commutes with the selected stabilizer Hamiltonian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L368-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L368-L377

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_hamiltonian
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) H.operator := by sorry
