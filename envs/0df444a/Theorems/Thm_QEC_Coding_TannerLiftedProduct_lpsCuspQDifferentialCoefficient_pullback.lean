-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspQDifferentialCoefficient_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:49.471022+00:00
-- url     : https://prove2.me/theorems/742a7876-1aa9-445a-a87b-6e7e0e8e3513
-- title:
--   Tanner Lifted Product: lps Cusp QDifferential Coefficient pullback
-- statement:
--   The filled-in coefficient pulls back to the original differential, not just a formal ratio.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L112-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L112-L120

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

theorem QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_pullback (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspQDifferentialCoefficient N f (Function.Periodic.qParam 1 τ) *
      (deriv (Function.Periodic.qParam 1) τ*v) = lpsCuspDifferential N f τ v := by sorry
