-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_parityBit_weight_le_one
-- name    : QEC.Coding.BDL26ReplacementSupport.parityBit_weight_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:30:56.841718+00:00
-- url     : https://prove2.me/theorems/4d42ede7-b956-4460-87ed-941d7c17810b
-- title:
--   BDL26 Replacement Support: parity Bit weight le one
-- statement:
--   The BDL26 Replacement Support construction uses the parity Bit weight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L142-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L142-L146

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

theorem QEC.Coding.BDL26ReplacementSupport.parityBit_weight_le_one {Coordinate : Type} [Fintype Coordinate]
    (word : Word Field Coordinate) : HammingWeight (parityBit word) ≤ 1 := by sorry
