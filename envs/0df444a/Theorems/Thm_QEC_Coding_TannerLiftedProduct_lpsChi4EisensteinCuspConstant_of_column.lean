-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspConstant_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:41.624257+00:00
-- url     : https://prove2.me/theorems/88ac28a1-9fd6-4a8e-8921-529419eecfdd
-- title:
--   Tanner Lifted Product: lps Chi4 Eisenstein Cusp Constant of column
-- statement:
--   Only two-adic valuation two supports the genuine modulus-four character constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L159-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L159-L175

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_of_column (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsChi4EisensteinCuspConstant γ=
      if t=2 then 3*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*
        lpsChi4E2Character (((γ 0 0*(L:ℤ)):ℤ):ZMod 4) else 0 := by sorry
