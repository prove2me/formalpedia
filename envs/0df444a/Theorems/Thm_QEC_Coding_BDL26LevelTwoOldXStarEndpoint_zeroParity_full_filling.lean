-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_zeroParity_full_filling
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.zeroParity_full_filling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:52:34.501135+00:00
-- url     : https://prove2.me/theorems/605399c2-38a8-442f-ae92-762a7babbfb7
-- title:
--   BDL26 Level Two Old XStar Endpoint: zero Parity full filling
-- statement:
--   ALL Q-edge and ALL Z-face components of a zero-parity physical filling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L544-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L544-L554

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.zeroParity_full_filling (S : OddScale) (r : Word F (C S).Q)
    (hc : rzCoboundary1 (P S) (rxState S baseState).admissible S r=0)
    (hp : rzQParity (P S) S r=0) :
    ∃ (edges : ∀ q : (P S).Q, Word F (QDoubleCylinderEdge (transposePresentation (P S)) q S))
      (faces : ∀ z : (P S).Z, Word F (ZDoubleCylinderFace (P S) z S)),
      rzCoboundary0 (P S) (rxState S baseState).admissible S
        ((∑ q,extendRZQEdgeWord (P S) S q (edges q))+
         (∑ z,extendRZFaceWord (P S) S z (faces z)))=r := by sorry
