-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_localLift_q_outside
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_q_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:48:41.199358+00:00
-- url     : https://prove2.me/theorems/a7638882-8b3f-459c-b20b-d00701d57f9b
-- title:
--   BDL26 Level Two Old XStar Endpoint: local Lift q outside
-- statement:
--   Connecting terms are retained; they vanish outside the actual neighbor set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L162-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L162-L177

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_q_outside (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (q : BaseQubit)
    (hq : Seed.xq x q≠true) (v : QDoubleCylinderVertex Seed q S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inr ⟨q,v⟩)=0 := by sorry
