-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_consumer
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_consumer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:57:54.287195+00:00
-- url     : https://prove2.me/theorems/acc45fcc-e21a-4543-a5bf-a54b336e10ce
-- title:
--   BDL26 RXQBlock Transport: map1 basis consumer
-- statement:
--   The BDL26 RXQBlock Transport construction uses the map1 basis consumer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L617-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L617-L631

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_consumer (q : QCoord S i) (a : Upper S depth i) :
    rootCoefficient S depth i h q a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))=1 ∧
      lowerWord S depth i h q a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))=
          canonicalBasisWord q ∧
      (coarseSum S depth i h a
        (a+((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord q))).val =
          (indexedFamily S depth).coboundary1 i.castSucc (canonicalBasisWord q) := by sorry
