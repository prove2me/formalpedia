-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_zSubdivisionBoundary_squared
-- name    : QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionBoundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:30:26.716206+00:00
-- url     : https://prove2.me/theorems/ec4b9776-9e29-43bb-8cfb-6a7be97acb8f
-- title:
--   BDL26 Finite Tanner Square: z Subdivision Boundary squared
-- statement:
--   The BDL26 Finite Tanner Square construction uses the z Subdivision Boundary squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2722-L2726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2722-L2726

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

theorem QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionBoundary_squared
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (subdivisionBoundary1 (transposePresentation P) z S).comp
      (subdivisionBoundary2 (transposePresentation P) z S) = 0 := by sorry
