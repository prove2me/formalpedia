-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_delta
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:40:31.47123+00:00
-- url     : https://prove2.me/theorems/cb767884-91c3-44ef-8b41-eac6f8406615
-- title:
--   BDL26 RXFinite Block Transport: remainder delta
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the remainder delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L387-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L387-L390

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_delta

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_delta (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (R S depth i h X0 a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by sorry
