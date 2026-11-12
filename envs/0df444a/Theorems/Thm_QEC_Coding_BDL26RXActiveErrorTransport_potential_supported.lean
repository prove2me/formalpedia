-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_potential_supported
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.potential_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:50:36.789815+00:00
-- url     : https://prove2.me/theorems/27a39cfa-0701-476f-9f54-0ee910bf1538
-- title:
--   BDL26 RXActive Error Transport: potential supported
-- statement:
--   The BDL26 RXActive Error Transport construction uses the potential supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L306-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L306-L309

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_supported

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.potential_supported (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h a b) ⊆
      BDL26RXFiniteBlockTransport.degreeZeroBlocks S depth i h (activeX S depth i h (a+b)) := by sorry
