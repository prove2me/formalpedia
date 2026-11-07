-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_norm_theta_coeff_mul_pow_of_le_two
-- name    : QEC.Coding.TannerLiftedProduct.summable_norm_theta_coeff_mul_pow_of_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:20.308713+00:00
-- url     : https://prove2.me/theorems/cb01d861-408f-46aa-818d-0ed8abb3c446
-- title:
--   Tanner Lifted Product: summable norm theta coeff mul pow of le two
-- statement:
--   A uniformly bounded natural coefficient sequence has a convergent
--   complex generating series in the open unit disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L23-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAnalyticTheta.lean#L23-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold

theorem QEC.Coding.TannerLiftedProduct.summable_norm_theta_coeff_mul_pow_of_le_two
    (S : PowerSeries ℕ)
    (hCoeff : ∀ n : ℕ, PowerSeries.coeff n S ≤ 2)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((PowerSeries.coeff n S : ℕ) : ℂ) * z ^ n‖) := by sorry
