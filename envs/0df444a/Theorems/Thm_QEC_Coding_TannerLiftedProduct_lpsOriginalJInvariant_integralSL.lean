-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_integralSL
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_integralSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:21.663781+00:00
-- url     : https://prove2.me/theorems/6c036dec-93d8-41b4-8860-9740fceb74da
-- title:
--   Tanner Lifted Product: lps Original JInvariant integral SL
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JInvariant integral SL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L26-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L26-L29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_integralSL (g : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJInvariant (g • τ)=lpsOriginalJInvariant τ := by sorry
