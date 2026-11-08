-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_F17LevelTwoBaseAdapter_stability_apply
-- name    : QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter.stability_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:47.001149+00:00
-- url     : https://prove2.me/theorems/80262b2f-30d6-496a-9bc3-d2577f4f81e8
-- title:
--   F17 Level Two Base Adapter: stability apply
-- statement:
--   The F17 Level Two Base Adapter construction uses the stability apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L287-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L287-L296

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
open QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}

theorem QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter.stability_apply
    (A : F17LevelTwoBaseAdapter D G hdepth)
    (I : StabilityBaseLevelTwoInput D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth))
    (hfit : I.supportFitsRadiusTwo)
    (hsyndrome : (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
      D.family.coboundary1 (levelTwoIndex hdepth) error) :
    error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier := by sorry
