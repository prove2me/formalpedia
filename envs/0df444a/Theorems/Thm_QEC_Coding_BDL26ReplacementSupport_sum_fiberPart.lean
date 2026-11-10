-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_sum_fiberPart
-- name    : QEC.Coding.BDL26ReplacementSupport.sum_fiberPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:16:19.170837+00:00
-- url     : https://prove2.me/theorems/f19ea62f-16b8-40a9-88ba-bd43e9d617df
-- title:
--   BDL26 Replacement Support: sum fiber Part
-- statement:
--   The BDL26 Replacement Support construction uses the sum fiber Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L66-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L66-L70

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
variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]

theorem QEC.Coding.BDL26ReplacementSupport.sum_fiberPart (owner : Coordinate → Label) (word : Word Field Coordinate) :
    (∑ label : Label, fiberPart owner label word) = word := by sorry
