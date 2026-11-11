-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
-- name    : QEC.Coding.BDL26RXQBlockTransport.lower_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:15:01.56575+00:00
-- url     : https://prove2.me/theorems/d6675b5a-8fc7-4034-aa4b-fd50282baa0d
-- title:
--   BDL26 RXQBlock Transport: lower syndrome
-- statement:
--   The BDL26 RXQBlock Transport construction uses the lower syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L391-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L391-L404

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

theorem QEC.Coding.BDL26RXQBlockTransport.lower_syndrome (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h q a b) =
      (coarseSum S depth i h a b).val := by sorry
