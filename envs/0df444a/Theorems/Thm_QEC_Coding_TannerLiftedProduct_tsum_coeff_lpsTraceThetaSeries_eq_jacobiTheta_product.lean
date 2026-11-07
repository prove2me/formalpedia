-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product
-- name    : QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:52.051219+00:00
-- url     : https://prove2.me/theorems/3a6f863b-6ac8-40ec-a113-7a3e07384949
-- title:
--   Tanner Lifted Product: tsum coeff lps Trace Theta Series eq jacobi Theta product
-- statement:
--   The LPS trace theta coefficients evaluate to the analytic product of
--   one ordinary Jacobi theta function and three scaled ones.  This is the
--   formal-to-analytic bridge needed before modular transformation and Fourier
--   coefficient estimates can be applied to the exact trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L323-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L323-L364

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      jacobiTheta τ *
        (jacobiTheta (((2 * r) ^ 2 : ℕ) * τ)) ^ 3 := by sorry
