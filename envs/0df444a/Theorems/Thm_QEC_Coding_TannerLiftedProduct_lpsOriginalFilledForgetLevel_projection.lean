-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:19.651335+00:00
-- url     : https://prove2.me/theorems/268456b9-f4c8-47f2-838b-961bf3917ee8
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level projection
-- statement:
--   The original filled-set map recovers the literal upper-half-plane projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L204-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L204-L205

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_projection (N M : ℕ) (hNM : N ∣ M) (τ : ℍ) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inl ⟦τ⟧) = Sum.inl ⟦τ⟧ := by sorry
