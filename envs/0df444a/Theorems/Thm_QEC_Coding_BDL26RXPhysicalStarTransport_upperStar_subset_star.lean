-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_upperStar_subset_star
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.upperStar_subset_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:35:05.468947+00:00
-- url     : https://prove2.me/theorems/ffca9bc9-5143-4135-9bde-89c55aa69314
-- title:
--   BDL26 RXPhysical Star Transport: upper Star subset star
-- statement:
--   The genuine physical star is contained in the original decoder block star.
--   The proof uses the actual full materialized coboundary, not an ownership oracle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L155-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L155-L160

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
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.upperStar_subset_star (u : FamilyX S depth i.succ) :
    upperStar S depth i u ⊆ star1 S depth i h (parentX S depth i h u) := by sorry
