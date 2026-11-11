-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_supported
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:09:06.368246+00:00
-- url     : https://prove2.me/theorems/115b705a-5a11-49e8-b967-3dfdd14c95ff
-- title:
--   BDL26 RXQBlock Transport: map1 basis supported
-- statement:
--   The actual lift of a basis is supported in its own actual Q block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L576-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L576-L591

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

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_supported (q : QCoord S i) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord q)) ⊆ (rxLq S depth i h).correctionRegion q := by sorry
