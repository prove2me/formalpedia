-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_mem_physicalXStar
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:04:43.646656+00:00
-- url     : https://prove2.me/theorems/6e59c094-57d7-4f62-a9f4-be3713f8162a
-- title:
--   BDL26 RXPhysical Star Transport: mem physical XStar
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the mem physical XStar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L31-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L31-L32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPhysicalStarTransport.mem_physicalXStar (P : TannerSquarePresentation) (x : P.X) (q : P.Q) :
    q ∈ physicalXStar P x ↔ P.xq x q=true := by sorry
