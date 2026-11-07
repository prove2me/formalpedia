-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_dvd_level
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_dvd_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:50.756301+00:00
-- url     : https://prove2.me/theorems/532b76a9-d3b2-4239-80b8-974913d6f846
-- title:
--   Tanner Lifted Product: lps Original Cusp Level Degree dvd level
-- statement:
--   The genuine cusp-level ratio divides the higher original level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L95-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L95-L101

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_dvd_level (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : lpsOriginalCuspLevelDegree N M ρ ∣ M := by sorry
