-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_inflate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:59.454205+00:00
-- url     : https://prove2.me/theorems/fe73cc9d-e937-4646-9f14-4a4745e30aa4
-- title:
--   Tanner Lifted Product: lps Char inflate
-- statement:
--   Inflating the modulus and argument by the same factor preserves the actual character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L49-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L49-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsChar_inflate (d m : ℕ) [NeZero d] [NeZero m] (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (x:ZMod d) := by sorry
