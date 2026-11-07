-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_mul_self
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:42.973325+00:00
-- url     : https://prove2.me/theorems/282a24d1-daf5-445e-a95f-c83d7f478121
-- title:
--   Decoder Dressed Logical: good Syndrome Projector mul self
-- statement:
--   The Decoder Dressed Logical construction uses the good Syndrome Projector mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L215-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L215-L228

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_mul_self
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    D.goodSyndromeProjector elementaryErrors *
        D.goodSyndromeProjector elementaryErrors =
      D.goodSyndromeProjector elementaryErrors := by sorry
