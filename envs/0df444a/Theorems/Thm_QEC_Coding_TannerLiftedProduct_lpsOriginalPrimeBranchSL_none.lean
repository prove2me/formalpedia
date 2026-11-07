-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_none
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:29:03.427037+00:00
-- url     : https://prove2.me/theorems/6264064a-39e1-413b-82d7-c8715f2355af
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL none
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L73-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L73-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_none (p : ℕ) :
    lpsOriginalPrimeBranchSL p none=1 := by sorry
