-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:42:54.14025+00:00
-- url     : https://prove2.me/theorems/7844ffb4-34c7-4547-965f-b449504673e7
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient pullback
-- statement:
--   The actual minimal-width coefficient pulls back to the original slash differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L72-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L72-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) *
      (deriv (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by sorry
