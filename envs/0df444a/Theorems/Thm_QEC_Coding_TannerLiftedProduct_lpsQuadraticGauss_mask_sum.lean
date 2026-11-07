-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_mask_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:35.652196+00:00
-- url     : https://prove2.me/theorems/613da7cf-2823-4873-9f17-6fa1d92578d9
-- title:
--   Tanner Lifted Product: lps Quadratic Gauss mask sum
-- statement:
--   The finite character mask projects the actual Gauss sum onto scaled residues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L149-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGaussSquare.lean#L149-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier (d*m) (a:ZMod (d*m))
      (((m:ℤ)*j.val:ℤ):ZMod (d*m))) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) := by sorry
