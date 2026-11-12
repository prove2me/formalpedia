-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_first_edge_cancellation_exterior
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:55:20.97918+00:00
-- url     : https://prove2.me/theorems/6a06dc95-a58c-475e-9e02-8ed5d84a3e13
-- title:
--   BDL26 RXActive Error Transport: first edge cancellation exterior
-- statement:
--   The BDL26 RXActive Error Transport construction uses the first edge cancellation exterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L637-L643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L637-L643

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_cancellation_exterior

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_exterior (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) (p : FamilyZ S depth (⟨0,hd⟩ : StepIndex depth).succ)
    (hp : p ∉ (rxData S depth ⟨0,hd⟩ (by rfl)).zSector) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i (by rfl) a b).val p=0 := by sorry
