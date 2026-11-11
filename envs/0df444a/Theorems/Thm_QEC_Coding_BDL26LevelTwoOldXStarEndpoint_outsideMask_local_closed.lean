-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_outsideMask_local_closed
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_local_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:46:23.657423+00:00
-- url     : https://prove2.me/theorems/1ab58780-1ae4-4f72-ab3e-08f6eff69823
-- title:
--   BDL26 Level Two Old XStar Endpoint: outside Mask local closed
-- statement:
--   The original cocycle supplies LOCAL face closedness of the mask.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L92-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L92-L99

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_local_closed (S : OddScale) (y : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) :
    wordLinearMapTranspose (doubleCylinderBoundary2 Seed y S)
      (fun e => outsideMask S y w (Sum.inl ⟨y,e⟩))=0 := by sorry
