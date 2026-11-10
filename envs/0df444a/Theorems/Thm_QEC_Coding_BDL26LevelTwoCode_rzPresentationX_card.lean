-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationX_card
-- name    : QEC.Coding.BDL26LevelTwoCode.rzPresentationX_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:05.413209+00:00
-- url     : https://prove2.me/theorems/10870f7d-ac9b-4e6e-970d-60294035cdac
-- title:
--   BDL26 Level Two Code: rz Presentation X card
-- statement:
--   Exact X-check count: Z-local faces, Q-local edges, and two copies of old X.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L94-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L94-L108

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.rzPresentationX_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).X =
      ((∑ z : P.Z,
        Fintype.card (ZDoubleCylinderFace P z S)) +
       (∑ q : P.Q,
        Fintype.card (QDoubleCylinderEdge (transposePresentation P) q S))) +
      Fintype.card P.X * 2 := by sorry
