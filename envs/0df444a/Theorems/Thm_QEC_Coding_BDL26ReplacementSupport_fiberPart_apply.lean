-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
-- name    : QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:16:08.124315+00:00
-- url     : https://prove2.me/theorems/70f76401-3daf-4e0c-b68d-620f647ba931
-- title:
--   BDL26 Replacement Support: fiber Part apply
-- statement:
--   The BDL26 Replacement Support construction uses the fiber Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L43-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L43-L46

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

theorem QEC.Coding.BDL26ReplacementSupport.fiberPart_apply (owner : Coordinate → Label) (label : Label)
    (word : Word Field Coordinate) (coordinate : Coordinate) :
    fiberPart owner label word coordinate =
      if owner coordinate = label then word coordinate else 0 := by sorry

attribute [defeq] QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
