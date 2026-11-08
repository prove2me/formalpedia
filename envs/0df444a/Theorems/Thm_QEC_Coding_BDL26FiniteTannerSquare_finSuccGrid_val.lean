-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_finSuccGrid_val
-- name    : QEC.Coding.BDL26FiniteTannerSquare.finSuccGrid_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:24:14.864268+00:00
-- url     : https://prove2.me/theorems/d5cc3837-a208-46a9-98fc-d7311f6d3ab8
-- title:
--   BDL26 Finite Tanner Square: fin Succ Grid val
-- statement:
--   The successor embedding into the finite grid increments the coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1222-L1223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L1222-L1223

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

theorem QEC.Coding.BDL26FiniteTannerSquare.finSuccGrid_val {m : Nat} (i : Fin m) :
    (finSuccGrid i).1 = i.1 + 1 := by sorry
