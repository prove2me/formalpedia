-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_mul_width
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_mul_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:47.327901+00:00
-- url     : https://prove2.me/theorems/0edb066d-cb56-4e9b-bcca-7cfb7342f07d
-- title:
--   Tanner Lifted Product: lps Original Cusp Level Degree mul width
-- statement:
--   The actual cusp-width ratio recovers the higher-level width exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L79-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L79-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_mul_width (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ * lpsOriginalCuspLevelDegree N M ρ =
      lpsOriginalCuspWidthNat M ρ := by sorry
