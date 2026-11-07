-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_slash_ratio
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_slash_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:13.088898+00:00
-- url     : https://prove2.me/theorems/922ea04d-65ad-401f-8305-7e265e69e1a0
-- title:
--   Tanner Lifted Product: lps Original JInvariant slash ratio
-- statement:
--   Exact general positive-GL ratio recovery includes determinant squared because pinned Mathlib slash uses determinant to weight minus1; used by original all-cusp recovery and the root fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L212-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L212-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_slash_ratio (M : GL (Fin 2) ℝ)
    (hM : 0<M.det.val) (τ : ℍ) :
    (M.det.val:ℂ)^2 * ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] M) τ^3 /
      ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] M) τ = lpsOriginalJInvariant (M•τ) := by sorry
