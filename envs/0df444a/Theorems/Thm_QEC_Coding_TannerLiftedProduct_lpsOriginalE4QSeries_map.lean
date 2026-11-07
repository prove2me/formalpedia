-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4QSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4QSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:15.432422+00:00
-- url     : https://prove2.me/theorems/e166c2df-d222-49be-ac0e-778040e95522
-- title:
--   Tanner Lifted Product: lps Original E4 QSeries map
-- statement:
--   The weight-four rational series maps to actual E4 q expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L105-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L105-L108

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4QSeries_map :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries 4)=
      qExpansion 1 ModularForm.E₄ := by sorry
