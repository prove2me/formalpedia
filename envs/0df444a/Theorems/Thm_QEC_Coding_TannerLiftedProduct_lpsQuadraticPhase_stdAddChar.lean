-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticPhase_stdAddChar
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticPhase_stdAddChar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:39.499754+00:00
-- url     : https://prove2.me/theorems/c2f71e33-b17d-468a-af92-4c854303ed3e
-- title:
--   Tanner Lifted Product: lps Quadratic Phase std Add Char
-- statement:
--   The existing analytic residue phase is the standard cyclic additive character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L73-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L73-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticPhase_stdAddChar (N : ℕ) [NeZero N] (a : ℤ) (r : Fin N) :
    lpsQuadraticPhase a N r = ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2) := by sorry
