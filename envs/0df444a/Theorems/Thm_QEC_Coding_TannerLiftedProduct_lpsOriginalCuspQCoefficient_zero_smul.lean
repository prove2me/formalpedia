-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_zero_smul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:13.3972+00:00
-- url     : https://prove2.me/theorems/2df20e10-fcc5-4237-8f4d-c4a92a05850b
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient zero smul
-- statement:
--   The actual removable cusp coefficient is complex-linear under positive-determinant translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L260-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L260-L288

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_zero_smul (N : ℕ) [NeZero N]
    (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : lpsOriginalCuspQCoefficient N (c • f) ρ 0=
      c*lpsOriginalCuspQCoefficient N f ρ 0 := by sorry
