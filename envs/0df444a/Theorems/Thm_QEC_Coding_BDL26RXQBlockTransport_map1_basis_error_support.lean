-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_error_support
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_basis_error_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:05:40.447354+00:00
-- url     : https://prove2.me/theorems/37613a5d-b7a9-473d-ad73-d42bf90c2a2e
-- title:
--   BDL26 RXQBlock Transport: map1 basis error support
-- statement:
--   The BDL26 RXQBlock Transport construction uses the map1 basis error support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L593-L597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L593-L597

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

theorem QEC.Coding.BDL26RXQBlockTransport.map1_basis_error_support (q : QCoord S i) (a : Upper S depth i) :
    hammingSupport (a+(a+((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord q))) ⊆ (rxLq S depth i h).correctionRegion q := by sorry
