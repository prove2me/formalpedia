-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_phaseOperator
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_phaseOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:49.402409+00:00
-- url     : https://prove2.me/theorems/4696f90c-931c-4f65-899a-0d7b2f096518
-- title:
--   Decoder Dressed Logical: syndrome Projector commute phase Operator
-- statement:
--   Every syndrome projector commutes with every decoder phase operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L286-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L286-L293

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_phaseOperator
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.phaseOperator logical) := by sorry
