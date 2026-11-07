-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaSlopeQSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeQSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:38.074061+00:00
-- url     : https://prove2.me/theorems/88383345-7f31-4a51-aa80-b199f7ffc10c
-- title:
--   Tanner Lifted Product: lps Original Delta Slope QSeries map
-- statement:
--   The actual rational shifted series maps to the genuine analytic divided-slope Taylor series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L166-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L166-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaSlopeQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalDeltaSlopeQSeries=
      lpsOriginalTaylorSeries (dslope (cuspFunction 1 ModularForm.discriminant) 0) := by sorry
