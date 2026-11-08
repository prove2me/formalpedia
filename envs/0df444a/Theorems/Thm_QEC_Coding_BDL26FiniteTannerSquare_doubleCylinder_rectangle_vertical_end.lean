-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinder_rectangle_vertical_end
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinder_rectangle_vertical_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:55.241257+00:00
-- url     : https://prove2.me/theorems/c07839f4-5d2a-4ac1-964f-ed173fcc7a22
-- title:
--   BDL26 Finite Tanner Square: double Cylinder rectangle vertical end
-- statement:
--   The BDL26 Finite Tanner Square construction uses the double Cylinder rectangle vertical end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2311-L2319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2311-L2319

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinder_rectangle_vertical_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (be : SubdivisionBoundaryEdge P x S)
    (hne : subdivisionBoundaryEdgeStart P x S be ≠
      subdivisionBoundaryEdgeEnd P x S be) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeEnd P x S be)) (Sum.inr be) = 1 := by sorry
