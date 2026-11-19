-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_unit_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_modulus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:39:02.15184+00:00
-- url     : https://prove2.me/theorems/326dbe46-636b-414d-8cb6-380f5d5c4259
-- title:
--   Tanner Lifted Product: lps SL2 Z first Column unit modulus
-- statement:
--   Determinant one provides an explicit inverse for the numerator modulo the denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L290-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspFactorization.lean#L290-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_modulus (N : ℕ) (γ : SL(2,ℤ))
    (hC : γ 1 0=(N:ℤ)) : IsUnit ((γ 0 0:ℤ):ZMod N) := by sorry
