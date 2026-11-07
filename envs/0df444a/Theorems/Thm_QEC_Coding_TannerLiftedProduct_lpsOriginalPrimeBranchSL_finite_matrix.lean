-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_finite_matrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:58.867184+00:00
-- url     : https://prove2.me/theorems/7e3184d7-d36e-4191-b914-0777c3f8d746
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL finite matrix
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL finite matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L76-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L76-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_matrix (p : ℕ) (m : Fin p) :
    (lpsOriginalPrimeBranchSL p (some m) : Matrix (Fin 2) (Fin 2) ℤ)=
      !![0,-1;1,(m.val:ℤ)] := by sorry
