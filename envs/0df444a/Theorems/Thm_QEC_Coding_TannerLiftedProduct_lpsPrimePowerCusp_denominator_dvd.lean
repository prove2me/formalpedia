-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCusp_denominator_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimePowerCusp_denominator_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:04.046348+00:00
-- url     : https://prove2.me/theorems/f21aafc1-6aef-40b2-8348-2538a89454ef
-- title:
--   Tanner Lifted Product: lps Prime Power Cusp denominator dvd
-- statement:
--   Denominator prime-power divisibility is exactly the exponent comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L149-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L149-L156

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsPrimePowerCusp_denominator_dvd (p e t L : ℕ) (hp : p.Prime) (hc : p.Coprime L) :
    (p:ℤ)^e∣((p^t*L:ℕ):ℤ) ↔ e≤t := by sorry
