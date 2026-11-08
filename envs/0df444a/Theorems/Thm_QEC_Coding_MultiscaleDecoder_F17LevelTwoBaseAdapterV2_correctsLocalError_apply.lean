-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_F17LevelTwoBaseAdapterV2_correctsLocalError_apply
-- name    : QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2.correctsLocalError_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:59.650397+00:00
-- url     : https://prove2.me/theorems/90b5e984-b5fc-4481-84ad-cbddfdf62542
-- title:
--   F17 Level Two Base Adapter V2: corrects Local Error apply
-- statement:
--   The F17 Level Two Base Adapter V2 construction uses the corrects Local Error apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L345-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L345-L356

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
open QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2.correctsLocalError_apply
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (A : F17LevelTwoBaseAdapterV2 D G hdepth)
    (hCorrects : A.CorrectsLocalErrors L)
    (I : LevelTwoSmallErrorInputV2 D hdepth)
    (hLocal : I.IsLocal L) :
    I.error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier := by sorry
