-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_not_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_not_dvd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:28:29.265675+00:00
-- url     : https://prove2.me/theorems/6ba4e72b-f058-42e2-b26b-e4bfb58b7fc4
-- title:
--   Tanner Lifted Product: lps Original Cusp Level Degree not dvd
-- statement:
--   The actual cusp-level ratio excludes every factor excluded from the higher level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L110-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean#L110-L113

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_not_dvd (N M p : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (hpM : ¬p ∣ M) (ρ : SL(2, ℤ)) : ¬p ∣ lpsOriginalCuspLevelDegree N M ρ := by sorry
