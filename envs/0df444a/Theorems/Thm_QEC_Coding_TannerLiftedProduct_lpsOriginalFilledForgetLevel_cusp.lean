-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:01.837346+00:00
-- url     : https://prove2.me/theorems/fb083f0a-a924-436f-b517-2e8264885228
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level cusp
-- statement:
--   The original filled-set map sends the represented genuine cusp to that same represented cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L208-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L208-L212

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cusp (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inr (lpsOriginalCuspOrbit M ρ)) =
      Sum.inr (lpsOriginalCuspOrbit N ρ) := by sorry
