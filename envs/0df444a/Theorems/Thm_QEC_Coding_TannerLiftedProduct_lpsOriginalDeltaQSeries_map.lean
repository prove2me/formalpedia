-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaQSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaQSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:15.915578+00:00
-- url     : https://prove2.me/theorems/c88af248-fe13-46dc-9fa7-af9096420b1d
-- title:
--   Tanner Lifted Product: lps Original Delta QSeries map
-- statement:
--   Actual rational Delta series maps to SAME actual Delta q expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L153-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L153-L159

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalDeltaQSeries=
      qExpansion 1 ModularForm.discriminant := by sorry
