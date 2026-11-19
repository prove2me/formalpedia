-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspConstant_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:30.369184+00:00
-- url     : https://prove2.me/theorems/3ff1ddc5-5dd0-4339-bfdd-871d49e14315
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp Constant of column
-- statement:
--   Only residue-prime valuation one supports the genuine quadratic character constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L178-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L178-L204

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_of_column (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsQuadraticEisensteinCuspConstant q γ=
      if v=1 then ((q:ℂ)^2-1)/gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))*
        lpsQuadraticE2Character q (((γ 0 0*(L:ℤ)):ℤ):ZMod q) else 0 := by sorry
