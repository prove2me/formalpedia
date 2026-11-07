-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:17.735268+00:00
-- url     : https://prove2.me/theorems/53f39ffa-b5ab-4bf1-8522-2c5a374b3293
-- title:
--   Tanner Lifted Product: lps Original Cusp Forget Level surjective
-- statement:
--   Every genuine lower-level cusp orbit has a higher-level preimage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L192-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L192-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_surjective (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalCuspForgetLevel N M hNM) := by sorry
