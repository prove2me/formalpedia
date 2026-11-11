-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_correction_regions_cover
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.correction_regions_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:39:13.012369+00:00
-- url     : https://prove2.me/theorems/4b3f3e89-9222-4e3d-8469-438d1db705f0
-- title:
--   BDL26 RXActive Error Transport: correction regions cover
-- statement:
--   These are the instantiated original decoder regions, covering every physical coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L107-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L107-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
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

theorem QEC.Coding.BDL26RXActiveErrorTransport.correction_regions_cover :
    (Finset.univ.biUnion ((rxLx S depth i h).correctionRegion)) ∪
      (Finset.univ.biUnion ((rxLq S depth i h).correctionRegion))=Finset.univ := by sorry
