-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_coarse_difference_apply
-- name    : QEC.Coding.BDL26RXQBlockTransport.coarse_difference_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:56:27.205227+00:00
-- url     : https://prove2.me/theorems/f30f0232-56c9-498a-9cfb-a31d2fbbca6a
-- title:
--   BDL26 RXQBlock Transport: coarse difference apply
-- statement:
--   The BDL26 RXQBlock Transport construction uses the coarse difference apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L413-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L413-L423

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

theorem QEC.Coding.BDL26RXQBlockTransport.coarse_difference_apply (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      if (state S i.val).presentation.qz q z=true then rootCoefficient S depth i h q a b else 0 := by sorry
