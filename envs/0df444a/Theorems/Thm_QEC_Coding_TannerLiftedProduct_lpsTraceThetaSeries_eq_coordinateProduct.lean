-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_coordinateProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_coordinateProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:38:36.188284+00:00
-- url     : https://prove2.me/theorems/4f83bc60-90a8-4af1-a40f-d545466a3a46
-- title:
--   Tanner Lifted Product: lps Trace Theta Series eq coordinate Product
-- statement:
--   The LPS trace theta series is coefficientwise the product of its four
--   unary diagonal factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L253-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L253-L262

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_coordinateProduct
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      ∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i := by sorry
