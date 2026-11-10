-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationQ_card
-- name    : QEC.Coding.BDL26LevelTwoCode.rzPresentationQ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:47:13.919995+00:00
-- url     : https://prove2.me/theorems/3e2273da-1afb-4411-a79d-d659f08a72f6
-- title:
--   BDL26 Level Two Code: rz Presentation Q card
-- statement:
--   Exact physical-qubit count from both disjoint RZ degree-one families.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L111-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L111-L131

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.rzPresentationQ_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Q =
      (∑ z : P.Z,
        Fintype.card (ZDoubleCylinderEdge P z S)) +
      (∑ q : P.Q,
        Fintype.card (QDoubleCylinderVertex (transposePresentation P) q S)) := by sorry
