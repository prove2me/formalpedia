-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_level_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_level_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:42.635304+00:00
-- url     : https://prove2.me/theorems/a05c6f4e-32d1-4403-a7ed-3deada45f7f1
-- title:
--   Tanner Lifted Product: lps Original Cusp Group level le
-- statement:
--   Actual inclusion of the conjugated cusp groups follows from original level divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L44-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_level_le (N M : ℕ) (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspGroup M ρ ≤ lpsOriginalCuspGroup N ρ := by sorry
