-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_level
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:45.736916+00:00
-- url     : https://prove2.me/theorems/7fb3073d-900d-4bcb-97f6-cff21cd25344
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat dvd level
-- statement:
--   The actual minimal original cusp width divides the original level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L52-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L52-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_level (N : ℕ) [NeZero N] (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ N := by sorry
