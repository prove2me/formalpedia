-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:29.966314+00:00
-- url     : https://prove2.me/theorems/54828dd1-d322-4c64-bf59-d5cf9d715f5b
-- title:
--   Tanner Lifted Product: lps Original Cusp Forget Level projection
-- statement:
--   The actual cusp map preserves the same integral representative acting on infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L184-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L184-L189

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_projection (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspForgetLevel N M hNM (lpsOriginalCuspOrbit M ρ) = lpsOriginalCuspOrbit N ρ := by sorry
