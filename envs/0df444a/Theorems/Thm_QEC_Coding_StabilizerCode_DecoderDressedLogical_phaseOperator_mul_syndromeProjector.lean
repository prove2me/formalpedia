-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_mul_syndromeProjector
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_mul_syndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:50.436542+00:00
-- url     : https://prove2.me/theorems/a5a17d36-037a-44e6-8f0b-0d66b7c52d43
-- title:
--   Decoder Dressed Logical: phase Operator mul syndrome Projector
-- statement:
--   A diagonal decoder phase acts by its scalar on one syndrome sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L258-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L258-L269

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_mul_syndromeProjector
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    D.phaseOperator logical * H.syndromeProjector syndrome =
      D.phase logical syndrome • H.syndromeProjector syndrome := by sorry
