-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_sharedQ_indicator_sum_zero
-- name    : QEC.Coding.BDL26FiniteTannerSquare.sharedQ_indicator_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:19:33.646841+00:00
-- url     : https://prove2.me/theorems/f5eac9dd-2d47-4400-80b6-40bd465e3368
-- title:
--   BDL26 Finite Tanner Square: shared Q indicator sum zero
-- statement:
--   A paired shared-Q fiber contributes zero in characteristic two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L362-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L362-L387

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

theorem QEC.Coding.BDL26FiniteTannerSquare.sharedQ_indicator_sum_zero (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    (∑ q : P.Q, if P.xq x q && P.qz q z then (1 : Field) else 0) = 0 := by sorry
