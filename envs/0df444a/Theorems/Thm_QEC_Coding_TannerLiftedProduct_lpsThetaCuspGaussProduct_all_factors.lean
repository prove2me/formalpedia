-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_all_factors
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_all_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:29.283264+00:00
-- url     : https://prove2.me/theorems/9a566837-c034-42c1-b207-d0e284b8fd69
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product all factors
-- statement:
--   The genuine Gauss product matches both correction factors at every positive denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L302-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L302-L337

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_all_factors (q N : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hN : 0<N) (γ : SL(2,ℤ)) (hC : γ 1 0=(N:ℤ)) :
    lpsThetaCuspGaussProduct q (γ 0 0) N=
      (4/3:ℂ)*(q:ℂ)^2/((q:ℂ)^2-1)*(N:ℂ)^2*
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by sorry
