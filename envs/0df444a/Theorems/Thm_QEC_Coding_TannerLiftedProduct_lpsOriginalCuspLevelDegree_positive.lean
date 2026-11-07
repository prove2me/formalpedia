-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_positive
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:25.359462+00:00
-- url     : https://prove2.me/theorems/9625d526-1055-4ee6-bb0c-0bc1eea26df3
-- title:
--   Tanner Lifted Product: lps Original Cusp Level Degree positive
-- statement:
--   The actual level ratio is positive, without a supplied ramification bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L86-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L86-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_positive (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : 0 < lpsOriginalCuspLevelDegree N M ρ := by sorry
