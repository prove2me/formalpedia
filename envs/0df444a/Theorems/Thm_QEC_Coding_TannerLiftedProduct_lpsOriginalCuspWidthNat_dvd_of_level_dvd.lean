-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_of_level_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_level_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:36.902448+00:00
-- url     : https://prove2.me/theorems/6966055f-a027-4bf9-9434-0a160b7a6562
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat dvd of level dvd
-- statement:
--   The actual minimum at the smaller level divides the actual higher-level minimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L62-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L62-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_level_dvd (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat M ρ := by sorry
