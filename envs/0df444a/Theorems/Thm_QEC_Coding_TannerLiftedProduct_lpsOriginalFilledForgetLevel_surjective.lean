-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:30:14.049291+00:00
-- url     : https://prove2.me/theorems/285f8cae-aa1a-45fc-9f65-0344e5bb4668
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level surjective
-- statement:
--   The actual original filled-set level map is surjective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L215-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L215-L224

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_surjective (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalFilledForgetLevel N M hNM) := by sorry
