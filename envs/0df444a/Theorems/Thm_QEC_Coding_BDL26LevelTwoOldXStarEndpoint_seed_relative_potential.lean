-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_seed_relative_potential
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.seed_relative_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:49:31.05817+00:00
-- url     : https://prove2.me/theorems/c01aa284-3cb0-4527-a718-a4bba971b58f
-- title:
--   BDL26 Level Two Old XStar Endpoint: seed relative potential
-- statement:
--   Both complete seed cases; the remaining fifth coefficient is retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L252-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L252-L296

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.seed_relative_potential (x : BaseX) (k : Word F BaseQubit)
    (hc : tannerCoboundary1 Seed k=0)
    (hk : ∀ q, Seed.xq x q≠true → k q=0) :
    tannerCoboundary0 Seed (k 4 • canonicalBasisWord x)=k := by sorry
