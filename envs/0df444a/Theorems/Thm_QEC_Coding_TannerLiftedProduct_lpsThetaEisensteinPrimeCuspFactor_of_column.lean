-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinPrimeCuspFactor_of_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinPrimeCuspFactor_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:29.778195+00:00
-- url     : https://prove2.me/theorems/00fe40c2-3997-4c6f-b51f-ba6929e18a4a
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Prime Cusp Factor of column
-- statement:
--   Evaluate the complete residue-prime gcd vector at every valuation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L122-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L122-L146

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinPrimeCuspFactor_of_column (q v L : ℕ) [Fact q.Prime]
    (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsThetaEisensteinPrimeCuspFactor q γ=
      if v=0 then ((q:ℂ)^2-1)/(q:ℂ)^2 else if v=1 then 0 else (q:ℂ)*((q:ℂ)^2-1) := by sorry
