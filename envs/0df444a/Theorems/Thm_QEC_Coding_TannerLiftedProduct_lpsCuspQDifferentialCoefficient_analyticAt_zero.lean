-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspQDifferentialCoefficient_analyticAt_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_analyticAt_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:29:34.876377+00:00
-- url     : https://prove2.me/theorems/4806c666-9b0c-448a-a20b-7d4588001923
-- title:
--   Tanner Lifted Product: lps Cusp QDifferential Coefficient analytic At zero
-- statement:
--   Actual cusp vanishing removes the apparent differential pole at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L25-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L25-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_analyticAt_zero (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    AnalyticAt ℂ (lpsCuspQDifferentialCoefficient N f) 0 := by sorry
