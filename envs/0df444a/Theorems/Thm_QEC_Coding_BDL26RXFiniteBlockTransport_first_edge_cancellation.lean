-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:08:31.6592+00:00
-- url     : https://prove2.me/theorems/dde6abf6-f903-4b32-8e87-518a3fab3fa4
-- title:
--   BDL26 RXFinite Block Transport: first edge cancellation
-- statement:
--   Concrete partial cancellation, with nonzero true lower/coarse words and both original corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L810-L833
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L810-L833

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    Localized S depth i (by rfl) ∅ {(0 : BaseQubit),(4 : BaseQubit)} a b ∧
      L S depth i (by rfl) ∅ a b=seedWord ∧
      L S depth i (by rfl) ∅ a b≠0 ∧
      (run S depth i (by rfl) b).correction=(run S depth i (by rfl) a).correction ∧
      (coarseSum S depth i (by rfl) a b).val (0 : BaseZ)=0 ∧
      (coarseSum S depth i (by rfl) a b).val (1 : BaseZ)=1 := by sorry
