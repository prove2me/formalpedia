-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_lowerError_physical_q_basis
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_physical_q_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:35:39.498792+00:00
-- url     : https://prove2.me/theorems/6214f45c-aa33-463d-9ae2-e45f6ff716a3
-- title:
--   BDL26 RZFinite Block Transport: lower Error physical q basis
-- statement:
--   Every physical Q vertex, including either retained copy, gives its old q basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L934-L947
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L934-L947

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.lowerError_physical_q_basis (a : Upper S depth i) (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    lowerError S depth i odd a
      (a+(read1 S depth i odd).symm (canonicalBasisWord (Sum.inr ⟨q,v⟩)))=
      canonicalBasisWord q := by sorry
