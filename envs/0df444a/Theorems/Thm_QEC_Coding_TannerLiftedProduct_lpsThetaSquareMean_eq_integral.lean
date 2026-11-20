-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareMean_eq_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:31:30.631992+00:00
-- url     : https://prove2.me/theorems/45ff2a0c-5c8f-4b0b-9476-6598e5ea4070
-- title:
--   Tanner Lifted Product: lps Theta Square Mean eq integral
-- statement:
--   The actual LPS square mean is the integral of the true theta-minus-complete-correction function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L39-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L39-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_eq_integral (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (y : ℝ) (hy : 0<y) :
    lpsThetaSquareMean q hq4 y=
      ∫ x in (0:ℝ)..1, ‖lpsStandardTheta q (lpsHorocyclePoint y hy x)-
        lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4)
          (lpsHorocyclePoint y hy x)‖^2 := by sorry
