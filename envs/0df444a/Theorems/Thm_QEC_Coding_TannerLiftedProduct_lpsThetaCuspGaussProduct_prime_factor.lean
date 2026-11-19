-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_prime_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:17.336199+00:00
-- url     : https://prove2.me/theorems/f7bb5829-f7e8-407b-9355-75fc2d8b6db7
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product prime factor
-- statement:
--   The actual residue-prime Gauss factor equals the full gcd-character cusp factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L247-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L247-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_factor (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ))
    (ha : IsUnit ((γ 0 0 * (L : ℤ) : ℤ) : ZMod (q ^ v))) :
    lpsThetaCuspGaussProduct q (γ 0 0*(L:ℤ)) (q^v)=
      (q:ℂ)^2/((q:ℂ)^2-1)*((q^v:ℕ):ℂ)^2*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by sorry
