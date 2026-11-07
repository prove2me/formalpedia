-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedZ_adjoint
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:38.400191+00:00
-- url     : https://prove2.me/theorems/389d365c-610b-4e64-a867-b103819bc816
-- title:
--   Decoder Dressed Logical: dressed Z adjoint
-- statement:
--   The Decoder Dressed Logical construction uses the dressed Z adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L506-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L506-L508

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedZ_adjoint (D : DecoderDressedLogical H) :
    LinearMap.adjoint D.dressedZ = D.dressedZ := by sorry
