-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_neighborhood_relative_exact
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.neighborhood_relative_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:48:32.921887+00:00
-- url     : https://prove2.me/theorems/11d65313-ce03-43de-b972-59b33441a143
-- title:
--   BDL26 Level Two Old XStar Endpoint: neighborhood relative exact
-- statement:
--   Construct relative exactness on the full neighborhood plus two coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L299-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L299-L357

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.neighborhood_relative_exact (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∃ g : V1 S, rxCoboundary0 Seed S g=w := by sorry
