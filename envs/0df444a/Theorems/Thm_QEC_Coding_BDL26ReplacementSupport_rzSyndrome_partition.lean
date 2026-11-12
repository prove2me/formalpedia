-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzSyndrome_partition
-- name    : QEC.Coding.BDL26ReplacementSupport.rzSyndrome_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:57:50.13237+00:00
-- url     : https://prove2.me/theorems/26f6903b-5a36-40e8-90d7-3ae8ea3f8ebe
-- title:
--   BDL26 Replacement Support: rz Syndrome partition
-- statement:
--   The BDL26 Replacement Support construction uses the rz Syndrome partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L131-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L131-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rzSyndrome_partition (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZZ P S)) :
    (∑ z : P.Z, fiberPart (rzSyndromeOwner P S) z word) = word := by sorry
