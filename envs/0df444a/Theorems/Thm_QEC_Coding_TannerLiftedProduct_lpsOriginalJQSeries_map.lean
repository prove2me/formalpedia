-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:44.311017+00:00
-- url     : https://prove2.me/theorems/bbce9a73-30d1-444c-94d1-2717b0600306
-- title:
--   Tanner Lifted Product: lps Original JQSeries map
-- statement:
--   Actual rational q-times-j series maps to SAME original analytic K Taylor series by neighborhood multiplication and true formal-unit cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L206-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L206-L242

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalJQSeries=
      lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by sorry
