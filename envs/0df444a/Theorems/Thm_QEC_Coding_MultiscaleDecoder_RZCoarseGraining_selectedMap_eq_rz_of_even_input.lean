-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_selectedMap_eq_rz_of_even_input
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.selectedMap_eq_rz_of_even_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:28.88245+00:00
-- url     : https://prove2.me/theorems/d5db8e59-cb0b-49f0-aae8-40714eb022bf
-- title:
--   RZCoarse Graining: selected Map eq rz of even input
-- statement:
--   The RZCoarse Graining construction uses the selected Map eq rz of even input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L222-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L222-L229

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.selectedMap_eq_rz_of_even_input
    (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth)
    (hEven : i.succ.val % 2 = 0) :
    D.selectedMap i = D.rzMap i := by sorry
