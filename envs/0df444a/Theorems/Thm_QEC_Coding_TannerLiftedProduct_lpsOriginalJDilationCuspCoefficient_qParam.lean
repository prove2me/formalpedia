-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspCoefficient_qParam
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_qParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:49.482282+00:00
-- url     : https://prove2.me/theorems/53251532-d5fd-4d0c-808b-b7fc790a1aba
-- title:
--   Tanner Lifted Product: lps Original JDilation Cusp Coefficient q Param
-- statement:
--   The actual q-coordinate coefficient recovers j(Ntau) after the original integral cusp representative; used by all nonzero filled-disc parameters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L266-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L266-L278

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_qParam (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJDilationCuspCoefficient N hN ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty (τ:ℂ))=
      lpsOriginalJDilated N hN (Matrix.SpecialLinearGroup.mapGL ℝ ρ•τ) := by sorry
