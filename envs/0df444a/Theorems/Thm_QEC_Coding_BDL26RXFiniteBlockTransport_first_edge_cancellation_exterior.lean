-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation_exterior
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:19:45.978424+00:00
-- url     : https://prove2.me/theorems/46f3215e-d40f-4c32-bfdc-224a1cce1f71
-- title:
--   BDL26 RXFinite Block Transport: first edge cancellation exterior
-- statement:
--   Cancellation leaves the actual selected image zero on every exterior coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L864-L872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L864-L872

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_cancellation_exterior (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (p : FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ)
    (hp : p ∉ (rxData S depth ⟨0,hd⟩ (by rfl)).zSector) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val p=0 := by sorry
