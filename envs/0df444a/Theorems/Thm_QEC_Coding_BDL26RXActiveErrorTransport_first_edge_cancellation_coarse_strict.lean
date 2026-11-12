-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_first_edge_cancellation_coarse_strict
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_coarse_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:51:21.87601+00:00
-- url     : https://prove2.me/theorems/ae55035d-6cd5-4f78-ba31-13dd04f494e9
-- title:
--   BDL26 RXActive Error Transport: first edge cancellation coarse strict
-- statement:
--   The BDL26 RXActive Error Transport construction uses the first edge cancellation coarse strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L615-L625
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L615-L625

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_coarse_strict (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    hammingSupport (coarseSum S depth i (by rfl) a b).val≠NZ S depth i (by rfl) a b := by sorry
