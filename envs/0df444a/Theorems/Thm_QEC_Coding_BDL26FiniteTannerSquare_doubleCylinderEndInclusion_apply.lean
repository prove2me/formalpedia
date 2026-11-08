-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
-- name    : QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:25.657257+00:00
-- url     : https://prove2.me/theorems/98910b2c-9135-4787-b88e-4562199f02e3
-- title:
--   BDL26 Finite Tanner Square: double Cylinder End Inclusion apply
-- statement:
--   The BDL26 Finite Tanner Square construction uses the double Cylinder End Inclusion apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2653-L2658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L2653-L2658

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

theorem QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (w : Word Field (SubdivisionVertex P x S))
    (v : SubdivisionVertex P x S) :
    doubleCylinderEndInclusion P x S t w (t, v) = w v := by sorry
