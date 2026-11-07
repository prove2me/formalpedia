-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsStandardTheta
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsStandardTheta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:40:52.952502+00:00
-- url     : https://prove2.me/theorems/4285c997-79a1-480e-9437-a6452c4d058d
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Standard Theta
-- statement:
--   Mathlib's analytic `qExpansion` of the normalized LPS theta product has
--   the coefficients of the already-formalized four-variable trace theta series.
--   No modular-form transformation law is assumed or concluded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L560-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L560-L571

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) (n : ℕ) :
    PowerSeries.coeff n
        (UpperHalfPlane.qExpansion 1
          (fun z : ℍ => lpsStandardTheta r z)) =
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) := by sorry
