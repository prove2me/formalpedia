-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalEisensteinQSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalEisensteinQSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:12.929945+00:00
-- url     : https://prove2.me/theorems/022f750f-d32b-45bf-9d19-a446122863ea
-- title:
--   Tanner Lifted Product: lps Original Eisenstein QSeries map
-- statement:
--   That concrete rational series maps to the SAME actual normalized Eisenstein q expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L96-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L96-L102

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalEisensteinQSeries_map (k : ℕ) (hk : 3≤k) (hk2 : Even k) :
    PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalEisensteinQSeries k)=
      qExpansion 1 (ModularForm.E hk) := by sorry
