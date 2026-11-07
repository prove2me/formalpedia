-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedZ
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:20.346205+00:00
-- url     : https://prove2.me/theorems/977efc73-da84-483d-9bf5-6ea963d7d50e
-- title:
--   Decoder Dressed Logical: good Syndrome Projector commute dressed Z
-- statement:
--   The good projector commutes with the dressed logical `Z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L361-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L361-L365

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedZ
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedZ := by sorry
