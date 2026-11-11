-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.lower_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:17:13.711681+00:00
-- url     : https://prove2.me/theorems/f05ac831-2a18-4c04-af3b-9e696bdcbad4
-- title:
--   BDL26 RXFinite Block Transport: lower syndrome
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the lower syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L468-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L468-L480

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.lower_syndrome (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
      (coarseSum S depth i h a b).val := by sorry
