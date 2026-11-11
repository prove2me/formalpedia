-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation_coarse_nonzero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation_coarse_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:33:12.957334+00:00
-- url     : https://prove2.me/theorems/0dc7a3d2-f99c-4675-a013-0f18ff512360
-- title:
--   BDL26 RXFinite Block Transport: first edge cancellation coarse nonzero
-- statement:
--   The uncancelled Z-one coefficient certifies a nonzero actual coarse word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L852-L861
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L852-L861

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation_coarse_nonzero (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    (coarseSum S depth i (by rfl) a b).val≠0 := by sorry
