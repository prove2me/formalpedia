-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_qParam
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_qParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:50.186039+00:00
-- url     : https://prove2.me/theorems/276fd5e2-c077-4148-8c9e-3bb4b4364d35
-- title:
--   Tanner Lifted Product: lps Original Cusp Level Degree q Param
-- statement:
--   The literal original exponential coordinates satisfy the exact integral power formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L116-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L116-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_qParam (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (z : ℂ) :
    Function.Periodic.qParam (lpsOriginalCuspGroup M ρ).strictWidthInfty z ^
      lpsOriginalCuspLevelDegree N M ρ =
        Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty z := by sorry
