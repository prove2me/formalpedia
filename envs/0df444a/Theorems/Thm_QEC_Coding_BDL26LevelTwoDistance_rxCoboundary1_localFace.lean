-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCoboundary1_localFace
-- name    : QEC.Coding.BDL26LevelTwoDistance.rxCoboundary1_localFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:35:25.700591+00:00
-- url     : https://prove2.me/theorems/c4fc5eb2-fa71-4626-898a-80b88ea8fd7f
-- title:
--   BDL26 Level Two Distance: rx Coboundary1 local Face
-- statement:
--   Actual RX syndrome restricted to an X-local face is exactly the local
--   face coboundary of the X-edge restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1063-L1082
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1063-L1082

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph

theorem QEC.Coding.BDL26LevelTwoDistance.rxCoboundary1_localFace (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (x : P.X) (face : DoubleCylinderFace P x S) :
    rxCoboundary1 P S word (Sum.inl (Sum.inl ⟨x, face⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun edge => word (Sum.inl ⟨x, edge⟩)) face := by sorry
