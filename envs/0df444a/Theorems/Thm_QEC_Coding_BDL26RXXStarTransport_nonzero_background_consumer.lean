-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_nonzero_background_consumer
-- name    : QEC.Coding.BDL26RXXStarTransport.nonzero_background_consumer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:58:49.142201+00:00
-- url     : https://prove2.me/theorems/f07e2e1b-bd81-44da-83ca-c04b28e24b7b
-- title:
--   BDL26 RXXStar Transport: nonzero background consumer
-- statement:
--   The actual nonzero input-syndrome background from the merged Q-block theorem,
--   combined with the present strict-X perturbation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L530-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L530-L546

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.nonzero_background_consumer (x : XCoord S i) (q : QCoord S i) :
    let a := ((indexedDecoderData S depth).selectedMap i).map1 (canonicalBasisWord (F := BDL26Field) q)
    a ≠ 0 ∧
    (errorSyndrome S depth i a).val
        ((rxData S depth i h).induced.zPairEquiv (BDL26RXQBlockTransport.incidentWitness S i q,0)).val=1 ∧
    OneX S depth i h x a (a+gradientError S depth i h x) ∧
    potential S depth i h x a (a+gradientError S depth i h x) ≠ 0 ∧
    ((indexedDecoderData S depth).selectedMap i).map1
        (lowerWord S depth i h x a (a+gradientError S depth i h x)) =
      updated S depth i h a (a+gradientError S depth i h x) +
        (indexedFamily S depth).coboundary0 i.succ
          (potential S depth i h x a (a+gradientError S depth i h x)) := by sorry
