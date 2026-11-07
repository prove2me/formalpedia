-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_qParam
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_qParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:43:07.100203+00:00
-- url     : https://prove2.me/theorems/4262bcf1-ffa9-446a-9fb3-d0784f96de34
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient q Param
-- statement:
--   The removable coefficient equals the same slash differential away from the cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L43-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L43-L69

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_qParam (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) =
      ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) *
        (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ) /
        (((2:ℂ)*Real.pi*I)*
          Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) := by sorry
