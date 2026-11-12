-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_first_edge_cancellation_active
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:52:19.33364+00:00
-- url     : https://prove2.me/theorems/fae17857-a19c-4a47-8ec1-acb47a58571a
-- title:
--   BDL26 RXActive Error Transport: first edge cancellation active
-- statement:
--   Both original seed labels are extracted from the actual original ERROR difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L590-L613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L590-L613

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.first_edge_cancellation_active (S : OddScale) (depth : Nat) (hd : 0<depth)
    (a : Upper S depth ⟨0,hd⟩) :
    let i : StepIndex depth := ⟨0,hd⟩
    let b := a+((indexedDecoderData S depth).selectedMap i).map1 BDL26RXFiniteBlockTransport.seedWord
    activeX S depth i (by rfl) (a+b)=∅ ∧
      activeQ S depth i (by rfl) (a+b)={(0 : BaseQubit),(4 : BaseQubit)} ∧
      L S depth i (by rfl) a b=BDL26RXFiniteBlockTransport.seedWord ∧
      HammingWeight (L S depth i (by rfl) a b) ≤ 2 ∧
      L S depth i (by rfl) a b≠0 ∧
      (coarseSum S depth i (by rfl) a b).val (0 : BaseZ)=0 ∧
      (coarseSum S depth i (by rfl) a b).val (1 : BaseZ)=1 ∧
      (coarseSum S depth i (by rfl) a b).val≠0 := by sorry
