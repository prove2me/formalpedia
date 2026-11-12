-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_piece_unions_disjoint
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.active_piece_unions_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:40:44.418186+00:00
-- url     : https://prove2.me/theorems/16d99cd6-cfa2-4b9c-bd6f-3326dc5e0d8a
-- title:
--   BDL26 RXActive Error Transport: active piece unions disjoint
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active piece unions disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L140-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L140-L148

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.active_piece_unions_disjoint (E : Upper S depth i) :
    Disjoint ((activeX S depth i h E).biUnion (xPiece S depth i h E))
      ((activeQ S depth i h E).biUnion (qPiece S depth i h E)) := by sorry
