-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_map1_eq_remainder
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.map1_eq_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:50:25.786198+00:00
-- url     : https://prove2.me/theorems/fb852401-e355-4db5-aee1-b23a78700b5a
-- title:
--   BDL26 RXActive Error Transport: map1 eq remainder
-- statement:
--   The BDL26 RXActive Error Transport construction uses the map1 eq remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L293-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L293-L295

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.map1_eq_remainder (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b)=R S depth i h a b := by sorry
