-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_j
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:30:33.704987+00:00
-- url     : https://prove2.me/theorems/c433d9d1-755c-4fb6-98f0-66a58a0b2468
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level j
-- statement:
--   The same original filled j function commutes with actual level descent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L227-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L227-L231

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_j (N M : ℕ) (hNM : N ∣ M) (x : LPSOriginalFilledCurve M) :
    lpsOriginalFilledJ N (lpsOriginalFilledForgetLevel N M hNM x) = lpsOriginalFilledJ M x := by sorry
