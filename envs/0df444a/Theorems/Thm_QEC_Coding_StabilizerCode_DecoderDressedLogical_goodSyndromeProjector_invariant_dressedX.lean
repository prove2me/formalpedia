-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_invariant_dressedX
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_invariant_dressedX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:57.787198+00:00
-- url     : https://prove2.me/theorems/821e170a-9de8-43f6-8b0c-ea08f0bf8733
-- title:
--   Decoder Dressed Logical: good Syndrome Projector invariant dressed X
-- statement:
--   The good sector is invariant under the dressed logical `X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L380-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L380-L391

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_invariant_dressedX
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors * D.dressedX *
        D.goodSyndromeProjector elementaryErrors =
      D.dressedX * D.goodSyndromeProjector elementaryErrors := by sorry
