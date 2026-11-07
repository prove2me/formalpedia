-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_sq
-- name    : QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:36:05.024959+00:00
-- url     : https://prove2.me/theorems/c176ec34-1a34-4e45-87d3-2e5d41df58be
-- title:
--   Tanner Lifted Product: coeff integer Theta Series sq
-- statement:
--   The Tanner Lifted Product construction uses the coeff integer Theta Series sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L107-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L107-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_sq (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff (m ^ 2) integerThetaSeries = 2 := by sorry
