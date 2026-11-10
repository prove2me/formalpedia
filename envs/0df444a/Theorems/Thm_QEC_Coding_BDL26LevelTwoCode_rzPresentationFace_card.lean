-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationFace_card
-- name    : QEC.Coding.BDL26LevelTwoCode.rzPresentationFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:06.956258+00:00
-- url     : https://prove2.me/theorems/06f440ab-0964-4cd0-88fe-5858fd6fc722
-- title:
--   BDL26 Level Two Code: rz Presentation Face card
-- statement:
--   Exact face count, retaining local, Q-Z glue, and old-X-copy faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L147-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L147-L163

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.rzPresentationFace_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Face =
      (∑ z : P.Z,
        Fintype.card (ZDoubleCylinderFace P z S) * (2 * 2)) +
      ((∑ e : QZEdge P,
        Fintype.card (QDoubleCylinderEdge
          (transposePresentation P) e.1.1 S) * 2) +
       Fintype.card P.Face * 2) := by sorry
