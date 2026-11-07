-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate_modulus
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_inflate_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:18.005208+00:00
-- url     : https://prove2.me/theorems/3a01fff9-b2c3-4590-8475-c5ee80729d2a
-- title:
--   Tanner Lifted Product: lps Char inflate modulus
-- statement:
--   Character inflation with an explicitly identified modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L60-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L60-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsChar_inflate_modulus (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod N) = ZMod.stdAddChar (x:ZMod d) := by sorry
