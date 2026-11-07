-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phase_mul_self
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:20.996602+00:00
-- url     : https://prove2.me/theorems/4883aa2b-6d27-47c6-903f-353b32ac7be4
-- title:
--   Decoder Dressed Logical: phase mul self
-- statement:
--   The Decoder Dressed Logical construction uses the phase mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L266-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L266-L271

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.phase_mul_self (D : DecoderDressedLogical H)
    (logical : Binary ι) (syndrome : DecoderSyndrome κ) :
    D.phase logical syndrome * D.phase logical syndrome = 1 := by sorry
