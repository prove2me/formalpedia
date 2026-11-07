-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidth_dvd_of_positive_zmultiple
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidth_dvd_of_positive_zmultiple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:42.088871+00:00
-- url     : https://prove2.me/theorems/4584e78e-02d2-4486-b12d-d4d44dfe5d15
-- title:
--   Tanner Lifted Product: lps Original Cusp Width dvd of positive zmultiple
-- statement:
--   Positive integral real-period factors give genuine natural divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L27-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L27-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidth_dvd_of_positive_zmultiple (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (z : ℤ) (hz : z • (a : ℝ) = (b : ℝ)) : a ∣ b := by sorry
