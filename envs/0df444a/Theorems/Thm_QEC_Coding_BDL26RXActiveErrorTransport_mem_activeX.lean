-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_mem_activeX
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.mem_activeX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:13:18.128975+00:00
-- url     : https://prove2.me/theorems/af8ae8e9-b584-4e4d-bb13-b686a73544de
-- title:
--   BDL26 RXActive Error Transport: mem active X
-- statement:
--   The BDL26 RXActive Error Transport construction uses the mem active X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L44-L46

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.mem_activeX (E : Upper S depth i) (x : XCoord S i) :
    x ∈ activeX S depth i h E ↔ (xPiece S depth i h E x).Nonempty := by sorry
