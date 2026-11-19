-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCuspGcd
-- name    : QEC.Coding.TannerLiftedProduct.lpsPrimePowerCuspGcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:04.169219+00:00
-- url     : https://prove2.me/theorems/5a50ce98-6173-48fd-a4f5-47238066d2c5
-- title:
--   Tanner Lifted Product: lps Prime Power Cusp Gcd
-- statement:
--   A coprime cofactor leaves the exact minimum-exponent cusp gcd.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L87-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L87-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsPrimePowerCuspGcd (p a t L : ℕ) (hc : p.Coprime L) :
    Int.gcd ((p^a:ℕ):ℤ) ((p^t*L:ℕ):ℤ)=p^(min a t) := by sorry
