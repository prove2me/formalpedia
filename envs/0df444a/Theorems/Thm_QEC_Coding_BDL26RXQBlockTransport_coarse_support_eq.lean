-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_coarse_support_eq
-- name    : QEC.Coding.BDL26RXQBlockTransport.coarse_support_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:57:37.107301+00:00
-- url     : https://prove2.me/theorems/70ca2679-cb72-48c1-b1e9-6267a5a63245
-- title:
--   BDL26 RXQBlock Transport: coarse support eq
-- statement:
--   The BDL26 RXQBlock Transport construction uses the coarse support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L430-L438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L430-L438

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

theorem QEC.Coding.BDL26RXQBlockTransport.coarse_support_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport (coarseSum S depth i h a b).val =
      if rootCoefficient S depth i h q a b=0 then ∅ else incidentZ S i q := by sorry
