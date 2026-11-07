-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
-- name    : QEC.Coding.TannerLiftedProduct.lpsFin_cast_finEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:29.827392+00:00
-- url     : https://prove2.me/theorems/393076ac-583c-4b47-ab42-4fe53447b096
-- title:
--   Tanner Lifted Product: lps Fin cast fin Equiv
-- statement:
--   The residue equivalence agrees with the actual natural cast.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L66-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L66-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsFin_cast_finEquiv (N : ℕ) [NeZero N] (r : Fin N) :
    (r.val:ZMod N) = ZMod.finEquiv N r := by sorry
