-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_zSubdivisionCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:00.979514+00:00
-- url     : https://prove2.me/theorems/9c396946-711b-48e8-813b-0a14cd22b626
-- title:
--   BDL26 Finite Tanner Square: z Subdivision Coboundary squared
-- statement:
--   The BDL26 Finite Tanner Square construction uses the z Subdivision Coboundary squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2728-L2732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2728-L2732

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

theorem QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionCoboundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (subdivisionCoboundary1 (transposePresentation P) z S).comp
      (subdivisionCoboundary0 (transposePresentation P) z S) = 0 := by sorry
