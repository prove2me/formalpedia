-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
-- name    : QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:06:45.201552+00:00
-- url     : https://prove2.me/theorems/cc7c62ec-e056-4adf-b1ec-066faf362b44
-- title:
--   Multiscale Decoder: historical Zero Syndrome Input support Fits Radius Two
-- statement:
--   The Multiscale Decoder construction uses the historical Zero Syndrome Input support Fits Radius Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L1308-L1323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L1308-L1323

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
variable {depth : Nat}
open BDL26CochainFamily

theorem QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
    {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {V : LevelIndex depth → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (D : BDL26DecoderData depth C0 C1 C2)
    (G : DecodingGraphFamily depth V)
    (hdepth : 2 ≤ depth)
    (center : V (levelTwoIndex hdepth))
    (syndromeLocation : C2 (levelTwoIndex hdepth) → V (levelTwoIndex hdepth)) :
    (historicalZeroSyndromeInput D G hdepth center syndromeLocation).supportFitsRadiusTwo := by sorry
