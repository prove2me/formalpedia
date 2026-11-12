-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzLocalDelta1_fiber_support
-- name    : QEC.Coding.BDL26ReplacementSupport.rzLocalDelta1_fiber_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:00:00.784073+00:00
-- url     : https://prove2.me/theorems/6bf9abdf-97d4-495f-aa5a-76b8f8489f40
-- title:
--   BDL26 Replacement Support: rz Local Delta1 fiber support
-- statement:
--   Distinct Z fibers cannot interact through the local endpoint differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L407-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L407-L431

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

theorem QEC.Coding.BDL26ReplacementSupport.rzLocalDelta1_fiber_support
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (z : P.Z) (word : Word Field (RZQ P S)) :
    hammingSupport (rzLocalDelta1 P A S
      (fiberPart (rzCorrectionOwner P S) (.z z) word)) ⊆
        fiberRegion (rzSyndromeOwner P S) z := by sorry
