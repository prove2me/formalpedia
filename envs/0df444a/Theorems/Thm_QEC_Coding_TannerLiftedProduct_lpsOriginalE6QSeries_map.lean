-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE6QSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE6QSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:18.304105+00:00
-- url     : https://prove2.me/theorems/583895fc-d2a5-4533-9706-40290c93d2d1
-- title:
--   Tanner Lifted Product: lps Original E6 QSeries map
-- statement:
--   The weight-six rational series maps to actual E6 q expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L111-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L111-L114

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE6QSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 6)=
      qExpansion 1 ModularForm.E₆ := by sorry
