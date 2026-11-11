-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_background_endpoint
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_background_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:40:35.456431+00:00
-- url     : https://prove2.me/theorems/fb9e3984-3645-4394-84fb-95e9f00f72a6
-- title:
--   BDL26 Level Two Old XStar Endpoint: old X background endpoint
-- statement:
--   The original arbitrary background is preserved in BOTH actual decoder calls.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L669-L678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L669-L678

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_background_endpoint (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (a h : Word F (C S).Q)
    (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hs : firstSearch S (tannerCoboundary1 (C S) a)=some ws)
    (ht : firstSearch S (tannerCoboundary1 (C S) (a+h))=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=
      h+decode S (tannerCoboundary1 (C S) a)+decode S (tannerCoboundary1 (C S) (a+h)) := by sorry
