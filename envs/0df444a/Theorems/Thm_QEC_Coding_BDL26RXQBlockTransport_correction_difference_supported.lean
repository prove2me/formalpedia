-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
-- name    : QEC.Coding.BDL26RXQBlockTransport.correction_difference_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:21:15.595734+00:00
-- url     : https://prove2.me/theorems/f7ff4810-bbef-49e6-a25c-4fb6c568e00f
-- title:
--   BDL26 RXQBlock Transport: correction difference supported
-- statement:
--   The BDL26 RXQBlock Transport construction uses the correction difference supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L260-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L260-L267

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

theorem QEC.Coding.BDL26RXQBlockTransport.correction_difference_supported (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    hammingSupport ((run S depth i h a).correction + (run S depth i h b).correction) ⊆
      (rxLq S depth i h).correctionRegion q := by sorry
