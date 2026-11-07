-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_mul_phaseOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_mul_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:04.272799+00:00
-- url     : https://prove2.me/theorems/1c30932c-0e9d-4e50-a4cc-007140a057a5
-- title:
--   Decoder Dressed Logical: syndrome Projector mul phase Operator
-- statement:
--   The same diagonal action holds with the syndrome projector on the left.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L272-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L272-L283

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_mul_phaseOperator
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    H.syndromeProjector syndrome * D.phaseOperator logical =
      D.phase logical syndrome • H.syndromeProjector syndrome := by sorry
