-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralSLAction_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralSLAction_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:05.708972+00:00
-- url     : https://prove2.me/theorems/f648d85e-fd46-4317-98ce-975753392024
-- title:
--   Tanner Lifted Product: lps Original Integral SLAction eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integral SLAction eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L18-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L18-L24

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralSLAction_eq (g : SL(2,ℤ)) (τ : ℍ) :
    g • τ = Matrix.SpecialLinearGroup.mapGL ℝ g • τ := by sorry
