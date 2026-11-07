-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_commute
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:07.206913+00:00
-- url     : https://prove2.me/theorems/7262c055-c776-4407-bc4a-1a897f2d4fc5
-- title:
--   Tanner Lifted Product: lps Original JDilation commute
-- statement:
--   Actual integer matrix entries prove dilation-conjugate commutation; used by the genuine translated-SL subgroup inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L122-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L122-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_commute (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (k : ℤ) (hk : γ 1 0=(N:ℤ)*k) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) *
      lpsE2AffineMatrix N hN 0 =
      lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ := by sorry
