-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_star_phase
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.star_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:12:58.715561+00:00
-- url     : https://prove2.me/theorems/1a69ab07-5c2b-42a9-8a8c-1cbebf2f0a79
-- title:
--   Decoder Dressed Logical: star phase
-- statement:
--   The Decoder Dressed Logical construction uses the star phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L274-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L274-L279

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.star_phase (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) :
    star (D.phase logical syndrome) = D.phase logical syndrome := by sorry
