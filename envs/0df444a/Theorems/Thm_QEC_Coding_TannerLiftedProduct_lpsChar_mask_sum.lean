-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_mask_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsChar_mask_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:31.955212+00:00
-- url     : https://prove2.me/theorems/5a81b240-bb7d-40de-81fd-2ea8ea678cca
-- title:
--   Tanner Lifted Product: lps Char mask sum
-- statement:
--   Primitive character orthogonality evaluates the finite divisibility mask.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L80-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L80-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsChar_mask_sum (d m : ℕ) [NeZero d] [NeZero m] (r : ℤ) :
    (∑ j : Fin d, ZMod.stdAddChar (((m:ℤ)*j.val*r:ℤ):ZMod (d*m))) =
      if (r:ZMod d)=0 then (d:ℂ) else 0 := by sorry
