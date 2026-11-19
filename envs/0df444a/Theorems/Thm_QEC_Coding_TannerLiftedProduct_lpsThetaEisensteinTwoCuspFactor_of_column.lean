-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinTwoCuspFactor_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoCuspFactor_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:43.677809+00:00
-- url     : https://prove2.me/theorems/f1bd6f5f-9d1a-4c88-9b6b-d942ddca052e
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Two Cusp Factor of column
-- statement:
--   Evaluate the complete two-power gcd vector in all denominator valuation cases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L94-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L94-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinTwoCuspFactor_of_column (t L : ℕ) (hL : Odd L)
    (γ : SL(2,ℤ)) (hC : γ 1 0=((2^t*L:ℕ):ℤ)) :
    lpsThetaEisensteinTwoCuspFactor γ=
      if t=0 then 3/4 else if t=1 then 0 else if t=2 then 6 else if t=3 then 0 else -24 := by sorry
