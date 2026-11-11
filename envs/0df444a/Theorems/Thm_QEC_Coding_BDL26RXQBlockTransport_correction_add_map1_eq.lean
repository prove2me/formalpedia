-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_add_map1_eq
-- name    : QEC.Coding.BDL26RXQBlockTransport.correction_add_map1_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:06:58.492027+00:00
-- url     : https://prove2.me/theorems/e258668c-03a2-4de0-8594-53e59a1e36ee
-- title:
--   BDL26 RXQBlock Transport: correction add map1 eq
-- statement:
--   Original canonical corrections agree on every background under an actual map1 shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L544-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L544-L556

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

theorem QEC.Coding.BDL26RXQBlockTransport.correction_add_map1_eq (a : Upper S depth i) (w : Lower S depth i) :
    (run S depth i h (a+((indexedDecoderData S depth).selectedMap i).map1 w)).correction =
      (run S depth i h a).correction := by sorry
