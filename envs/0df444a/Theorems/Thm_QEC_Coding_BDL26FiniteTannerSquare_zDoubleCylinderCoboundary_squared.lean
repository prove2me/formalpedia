-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_zDoubleCylinderCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:30:59.509196+00:00
-- url     : https://prove2.me/theorems/aeea71a9-2641-4112-9520-5f0dc71503b2
-- title:
--   BDL26 Finite Tanner Square: z Double Cylinder Coboundary squared
-- statement:
--   The BDL26 Finite Tanner Square construction uses the z Double Cylinder Coboundary squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2750-L2754
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2750-L2754

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

theorem QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderCoboundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (doubleCylinderCoboundary1 (transposePresentation P) z S).comp
      (doubleCylinderCoboundary0 (transposePresentation P) z S) = 0 := by sorry
