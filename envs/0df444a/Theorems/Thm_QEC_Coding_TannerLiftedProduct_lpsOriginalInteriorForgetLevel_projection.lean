-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:20.238505+00:00
-- url     : https://prove2.me/theorems/6a8826f3-d0b7-4ac5-ae51-d4cddeaccde1
-- title:
--   Tanner Lifted Product: lps Original Interior Forget Level projection
-- statement:
--   The actual interior quotient map preserves the literal upper-half-plane representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L152-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L152-L153

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_projection (N M : ℕ) (hNM : N ∣ M) (τ : ℍ) :
    lpsOriginalInteriorForgetLevel N M hNM ⟦τ⟧ = ⟦τ⟧ := by sorry
