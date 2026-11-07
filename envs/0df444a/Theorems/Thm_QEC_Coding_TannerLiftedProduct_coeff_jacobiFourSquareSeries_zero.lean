-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:42.27749+00:00
-- url     : https://prove2.me/theorems/7ef7f1eb-9c81-472f-a0d5-8f55f9bc667d
-- title:
--   Tanner Lifted Product: coeff jacobi Four Square Series zero
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Four Square Series zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L236-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L236-L238

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero :
    PowerSeries.coeff 0 jacobiFourSquareSeries = 1 := by sorry
