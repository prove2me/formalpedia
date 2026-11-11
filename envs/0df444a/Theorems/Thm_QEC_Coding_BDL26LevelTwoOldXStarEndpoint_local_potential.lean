-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_local_potential
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.local_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:49:09.349114+00:00
-- url     : https://prove2.me/theorems/b5060296-99b2-4e01-8f3d-c8207fc0e22f
-- title:
--   BDL26 Level Two Old XStar Endpoint: local potential
-- statement:
--   Extract the distinguished cylinder potential from proved local H1=0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L192-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L192-L205

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.local_potential (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0) :
    ∃ f : Word F (DoubleCylinderVertex Seed x S),
      wordLinearMapTranspose (rxCx Seed x S).boundary1 f=
        fun e => w (Sum.inl ⟨x,e⟩) := by sorry
