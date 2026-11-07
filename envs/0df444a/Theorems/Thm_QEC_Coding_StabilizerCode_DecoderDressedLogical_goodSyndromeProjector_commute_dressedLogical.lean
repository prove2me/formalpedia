-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedLogical
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedLogical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:30.335662+00:00
-- url     : https://prove2.me/theorems/74aca3e9-6b86-428a-a345-7744b09160c3
-- title:
--   Decoder Dressed Logical: good Syndrome Projector commute dressed Logical
-- statement:
--   The good projector commutes with every dressed normalizer Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L340-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L340-L351

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedLogical
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.goodSyndromeProjector elementaryErrors)
      (D.dressedLogical logical) := by sorry
