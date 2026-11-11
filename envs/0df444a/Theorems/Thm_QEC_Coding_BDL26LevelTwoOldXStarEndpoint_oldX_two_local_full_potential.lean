-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_two_local_full_potential
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_two_local_full_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:33:07.057182+00:00
-- url     : https://prove2.me/theorems/b2449e99-de1d-4a44-9e73-efb885e5b1fe
-- title:
--   BDL26 Level Two Old XStar Endpoint: old X two local full potential
-- statement:
--   A full old-X-star word and two independently local original corrections
--   have a complete physical boundary potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L572-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L572-L647

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_two_local_full_potential (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (h d e : Word F (C S).Q)
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hd : levelTwoLocalError S d) (he : levelTwoLocalError S e)
    (hc : tannerCoboundary1 (C S) (h+d+e)=0) :
    ∃ (g : Word F (P S).X)
      (edges : ∀ q : (P S).Q, Word F (QDoubleCylinderEdge (transposePresentation (P S)) q S))
      (faces : ∀ z : (P S).Z, Word F (ZDoubleCylinderFace (P S) z S)),
      tannerCoboundary0 (C S)
        (oldXLift S g+
          (∑ q,(show Word F (C S).X from extendRZQEdgeWord (P S) S q (edges q)))+
          (∑ z,(show Word F (C S).X from extendRZFaceWord (P S) S z (faces z))))=h+d+e := by sorry
