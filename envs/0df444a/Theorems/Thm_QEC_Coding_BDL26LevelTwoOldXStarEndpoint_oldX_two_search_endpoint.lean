-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_two_search_endpoint
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_two_search_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:52:41.855105+00:00
-- url     : https://prove2.me/theorems/ccad28c3-2d68-427a-9df6-811914cf2bfb
-- title:
--   BDL26 Level Two Old XStar Endpoint: old X two search endpoint
-- statement:
--   Exact original two-search endpoint for arbitrary raw, possibly nonzero,
--   syndromes. No range certificate, earlier-zero convention or linearity is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L651-L666
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L651-L666

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
attribute [local instance] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldXActualQFintype

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_two_search_endpoint (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (C S).Q)
    (s t : Word F (C S).Z) (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hsyn : tannerCoboundary1 (C S) h=s+t)
    (hs : firstSearch S s=some ws) (ht : firstSearch S t=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=h+decode S s+decode S t := by sorry
