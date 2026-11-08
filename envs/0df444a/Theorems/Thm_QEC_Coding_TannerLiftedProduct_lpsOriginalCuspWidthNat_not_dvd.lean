-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_not_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_not_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:29:22.117142+00:00
-- url     : https://prove2.me/theorems/7a588047-1410-4d94-98dd-864b5e87637c
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat not dvd
-- statement:
--   A divisor of the level cannot acquire a prime factor excluded from that level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L104-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L104-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_not_dvd (N p : ℕ) [NeZero N]
    (hpN : ¬p ∣ N) (ρ : SL(2, ℤ)) : ¬p ∣ lpsOriginalCuspWidthNat N ρ := by sorry
