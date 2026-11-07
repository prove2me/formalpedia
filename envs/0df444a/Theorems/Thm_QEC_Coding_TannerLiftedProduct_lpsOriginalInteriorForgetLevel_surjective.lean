-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:17.997513+00:00
-- url     : https://prove2.me/theorems/7895ddbf-456c-4b14-8f69-e0135ad1e0a9
-- title:
--   Tanner Lifted Product: lps Original Interior Forget Level surjective
-- statement:
--   Every actual original lower-level interior orbit has a higher-level preimage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L156-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L156-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_surjective (N M : ℕ) (hNM : N ∣ M) :
    Function.Surjective (lpsOriginalInteriorForgetLevel N M hNM) := by sorry
