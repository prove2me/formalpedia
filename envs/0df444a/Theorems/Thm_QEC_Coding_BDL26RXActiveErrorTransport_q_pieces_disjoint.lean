-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_q_pieces_disjoint
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.q_pieces_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:41:46.487511+00:00
-- url     : https://prove2.me/theorems/369d445b-d724-4b82-b64a-d0cfebacdd51
-- title:
--   BDL26 RXActive Error Transport: q pieces disjoint
-- statement:
--   The BDL26 RXActive Error Transport construction uses the q pieces disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L133-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L133-L138

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.q_pieces_disjoint (E : Upper S depth i) (q r : QCoord S i) (hn : q≠r) :
    Disjoint (qPiece S depth i h E q) (qPiece S depth i h E r) := by sorry
