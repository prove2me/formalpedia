-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_character_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_character_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:18.900213+00:00
-- url     : https://prove2.me/theorems/fcb6f5f7-3a25-4ede-bfdb-7107abc2aa1a
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist cusp character tendsto
-- statement:
--   The actual quadratic twist has its full-filter character limit at every integer cusp matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L372-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L372-L394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_character_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsQuadraticEisensteinCuspConstant q γ)) := by sorry
