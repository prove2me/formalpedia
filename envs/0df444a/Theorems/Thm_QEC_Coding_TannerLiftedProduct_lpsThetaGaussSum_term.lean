-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaGaussSum_term
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:44:31.148534+00:00
-- url     : https://prove2.me/theorems/8990da37-b7ac-4e6d-af81-b480c451be39
-- title:
--   Tanner Lifted Product: lps Theta Gauss Sum term
-- statement:
--   Combine the quadratic residue phase and the genuine Jacobi linear phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L94-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean#L94-L106

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real

theorem QEC.Coding.TannerLiftedProduct.lpsThetaGaussSum_term (a n : ℤ) (N : ℕ) [NeZero N] (r : Fin N) (z : ℂ) :
    lpsQuadraticPhase a N r * jacobiTheta₂_term n ((r.val:ℂ)/(N:ℂ)) z =
      ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2+(n:ZMod N)*(ZMod.finEquiv N r)) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by sorry
