-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeQ
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.mem_activeQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:15:30.138949+00:00
-- url     : https://prove2.me/theorems/e2f41c73-b56d-412f-8325-0c2f6153bca3
-- title:
--   BDL26 RXActive Error Transport: mem active Q
-- statement:
--   The BDL26 RXActive Error Transport construction uses the mem active Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L48-L50

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.mem_activeQ (E : Upper S depth i) (q : QCoord S i) :
    q ∈ activeQ S depth i h E ↔ (qPiece S depth i h E q).Nonempty := by sorry
