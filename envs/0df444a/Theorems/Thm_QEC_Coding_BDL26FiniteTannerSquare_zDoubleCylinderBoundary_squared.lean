-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_zDoubleCylinderBoundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderBoundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:09.977968+00:00
-- url     : https://prove2.me/theorems/cad723ce-78d5-4829-b83c-d91f43ee66d1
-- title:
--   BDL26 Finite Tanner Square: z Double Cylinder Boundary squared
-- statement:
--   The BDL26 Finite Tanner Square construction uses the z Double Cylinder Boundary squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2744-L2748
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2744-L2748

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

theorem QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderBoundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (doubleCylinderBoundary1 (transposePresentation P) z S).comp
      (doubleCylinderBoundary2 (transposePresentation P) z S) = 0 := by sorry
