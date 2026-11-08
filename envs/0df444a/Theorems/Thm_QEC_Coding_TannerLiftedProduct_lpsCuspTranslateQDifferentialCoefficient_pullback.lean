-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspTranslateQDifferentialCoefficient_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspTranslateQDifferentialCoefficient_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:48.272356+00:00
-- url     : https://prove2.me/theorems/62ac9925-7a91-4646-9c6a-f88ebdecaad7
-- title:
--   Tanner Lifted Product: lps Cusp Translate QDifferential Coefficient pullback
-- statement:
--   At every rational cusp the same regular coefficient pulls back to the true slash differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L123-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean#L123-L133

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

theorem QEC.Coding.TannerLiftedProduct.lpsCuspTranslateQDifferentialCoefficient_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsCuspTranslateQDifferentialCoefficient N f ρ (Function.Periodic.qParam (N:ℝ) τ) *
      (deriv (Function.Periodic.qParam (N:ℝ)) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by sorry
