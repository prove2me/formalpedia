-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadratic_scaled_period
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadratic_scaled_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:31.425244+00:00
-- url     : https://prove2.me/theorems/87498988-e55f-4f97-84c8-e4efbebd2524
-- title:
--   Tanner Lifted Product: lps Quadratic scaled period
-- statement:
--   A scaled quadratic phase is periodic across the actual residue blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L98-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L98-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadratic_scaled_period (d m : ℕ) [NeZero d] [NeZero m]
    (a r i : ℤ) :
    ZMod.stdAddChar (((a*(d:ℤ)^2*(r+(m:ℤ)*i)^2):ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (((a*(d:ℤ)^2*r^2):ℤ):ZMod (d*m)) := by sorry
