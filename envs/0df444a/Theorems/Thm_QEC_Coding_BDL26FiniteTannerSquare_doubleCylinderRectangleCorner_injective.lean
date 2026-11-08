-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderRectangleCorner_injective
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderRectangleCorner_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:43.245971+00:00
-- url     : https://prove2.me/theorems/c1ffc681-b9e3-430d-95a3-39060b4a656e
-- title:
--   BDL26 Finite Tanner Square: double Cylinder Rectangle Corner injective
-- statement:
--   The four tagged rectangle corners are pairwise distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2346-L2354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2346-L2354

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

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderRectangleCorner_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    Function.Injective (doubleCylinderRectangleCorner P x S rectangle) := by sorry
