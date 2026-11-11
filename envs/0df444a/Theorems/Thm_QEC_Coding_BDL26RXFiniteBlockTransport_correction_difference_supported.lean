-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_correction_difference_supported
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.correction_difference_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:14:18.537122+00:00
-- url     : https://prove2.me/theorems/1c02a41e-06c6-4dc9-b505-a78aad65d1ae
-- title:
--   BDL26 RXFinite Block Transport: correction difference supported
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the correction difference supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L232-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L232-L262

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.correction_difference_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star S depth i h X0 Q0 := by sorry
