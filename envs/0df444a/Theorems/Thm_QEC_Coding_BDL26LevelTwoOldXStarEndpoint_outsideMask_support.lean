-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_outsideMask_support
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:46:15.471553+00:00
-- url     : https://prove2.me/theorems/c1e4656d-7028-4c1f-b639-4cb14e8ef8ac
-- title:
--   BDL26 Level Two Old XStar Endpoint: outside Mask support
-- statement:
--   The masked word, not the original neighborhood-supported word, has global
--   support in the two extra coordinates. Duplicates and missing labels are allowed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L75-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L75-L89

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_support (S : OddScale) (x y : BaseX) (hy : y≠x)
    (w : W1 S) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b) :
    ∀ r, outsideMask S y w r≠0 → r=a ∨ r=b := by sorry
