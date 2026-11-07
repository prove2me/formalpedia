-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspFunction_prod_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspFunction_prod_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:44.048382+00:00
-- url     : https://prove2.me/theorems/ff1c6487-ee04-4b4a-91e0-3342b9550945
-- title:
--   Tanner Lifted Product: lps Cusp Function prod analytic
-- statement:
--   A finite product of actual cusp functions is analytic at zero when each factor is analytic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L52-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L52-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsCuspFunction_prod_analytic {ι : Type*} (h : ℝ) (s : Finset ι) (F : ι→ℍ→ℂ)
    (ha : ∀i∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F i)) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (∏i∈s,F i)) 0 := by sorry
