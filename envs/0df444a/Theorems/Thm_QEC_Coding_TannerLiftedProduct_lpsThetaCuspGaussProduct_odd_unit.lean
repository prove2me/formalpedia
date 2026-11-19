-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_odd_unit
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_odd_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:31.949899+00:00
-- url     : https://prove2.me/theorems/16962061-c1a8-4248-8b0d-1cdc45cd5026
-- title:
--   Tanner Lifted Product: lps Theta Cusp Gauss Product odd unit
-- statement:
--   An odd cofactor coprime to twice the residue prime contributes its modulus squared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L87-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L87-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_odd_unit (q N : ℕ) [NeZero N] (hN : Odd N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) (hq : IsUnit ((2*q:ℕ):ZMod N)) :
    lpsThetaCuspGaussProduct q a N=(N:ℂ)^2 := by sorry
