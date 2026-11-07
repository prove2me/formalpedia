-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_one_sub_goodSyndromeProjector_eq_badSyndromeProjector
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.one_sub_goodSyndromeProjector_eq_badSyndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:41.112538+00:00
-- url     : https://prove2.me/theorems/d00a104a-fcca-4dac-97d8-a371badce074
-- title:
--   Decoder Dressed Logical: one sub good Syndrome Projector eq bad Syndrome Projector
-- statement:
--   The bad-sector projector is literally the complement of `P_good`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L249-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L249-L255

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.one_sub_goodSyndromeProjector_eq_badSyndromeProjector
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    1 - D.goodSyndromeProjector elementaryErrors =
      D.badSyndromeProjector elementaryErrors := by sorry
