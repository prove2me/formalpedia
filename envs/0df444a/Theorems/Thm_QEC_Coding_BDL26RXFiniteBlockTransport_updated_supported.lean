-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_updated_supported
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.updated_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:23:38.752123+00:00
-- url     : https://prove2.me/theorems/8d5a24e9-955c-4f67-888c-9f271750dcfb
-- title:
--   BDL26 RXFinite Block Transport: updated supported
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the updated supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L274-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L274-L287

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.updated_supported (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (updated S depth i h a b) ⊆ star S depth i h X0 Q0 := by sorry
