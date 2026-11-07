-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:39:06.163939+00:00
-- url     : https://prove2.me/theorems/82512370-00da-46ab-bf3f-b37343aa4277
-- title:
--   Tanner Lifted Product: coeff lps Trace Coordinate Theta Series prod eq card
-- statement:
--   The coefficient of the unary-product presentation counts its explicit
--   exponent/root witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L162-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean#L162-L173

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
    (q n : ℕ) :
    PowerSeries.coeff n
        (∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i) =
      Fintype.card (LPSTraceThetaWitness q n) := by sorry
