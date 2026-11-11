-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_basis_boundary_support
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.basis_boundary_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:12:22.539193+00:00
-- url     : https://prove2.me/theorems/e7fe6827-e07c-45d5-a805-526a7130208e
-- title:
--   BDL26 RXPhysical Star Transport: basis boundary support
-- statement:
--   The full global basis boundary, including connecting terms, has this exact support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L50-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L50-L55

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.basis_boundary_support (P : TannerSquarePresentation) (x : P.X) :
    hammingSupport (tannerCoboundary0 P (canonicalBasisWord x))=physicalXStar P x := by sorry
