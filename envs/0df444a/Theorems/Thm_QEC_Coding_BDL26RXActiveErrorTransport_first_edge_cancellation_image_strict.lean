-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_first_edge_cancellation_image_strict
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_image_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:56:07.218705+00:00
-- url     : https://prove2.me/theorems/511bddc8-36b4-4337-87fc-066d023904aa
-- title:
--   BDL26 RXActive Error Transport: first edge cancellation image strict
-- statement:
--   Partial cancellation also makes the actual upper image strictly smaller than the full neighbor image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L646-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L646-L685

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
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_image_strict (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val) ≠
      (NZ S depth i (by rfl) a b).biUnion (zPairImage (rxData S depth i (by rfl))) := by sorry
