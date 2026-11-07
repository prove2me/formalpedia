-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_adjoint
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:50.71783+00:00
-- url     : https://prove2.me/theorems/e30d8f41-6898-44d6-b536-3b45bf1c0104
-- title:
--   Decoder Dressed Logical: good Syndrome Projector adjoint
-- statement:
--   The Decoder Dressed Logical construction uses the good Syndrome Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L204-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L204-L212

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_adjoint
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    LinearMap.adjoint (D.goodSyndromeProjector elementaryErrors) =
      D.goodSyndromeProjector elementaryErrors := by sorry
