-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_upper_nonzero
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_upper_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:59:16.34556+00:00
-- url     : https://prove2.me/theorems/0378a19f-71a3-4527-8c88-aeb1bcb8ce91
-- title:
--   BDL26 RXQBlock Transport: map1 basis upper nonzero
-- statement:
--   The BDL26 RXQBlock Transport construction uses the map1 basis upper nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L659-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L659-L665

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

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_upper_nonzero (h : i.val % 2=0) (q : QCoord S i) :
    ((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord (F := BDL26Field) q) ≠ 0 := by sorry
