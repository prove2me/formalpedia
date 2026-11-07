-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasSum_lpsStandardTheta_coeff
-- name    : QEC.Coding.TannerLiftedProduct.hasSum_lpsStandardTheta_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:53.255441+00:00
-- url     : https://prove2.me/theorems/1bbd689d-6a3f-4fee-b8f4-f0183fd71c5a
-- title:
--   Tanner Lifted Product: has Sum lps Standard Theta coeff
-- statement:
--   The standard theta product is represented by its exact formal
--   coefficients in Mathlib's period-one `qParam` convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L484-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L484-L500

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.hasSum_lpsStandardTheta_coeff
    (r : ℕ) (hr : 0 < r) (z : ℍ) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n)
      (lpsStandardTheta r z) := by sorry
