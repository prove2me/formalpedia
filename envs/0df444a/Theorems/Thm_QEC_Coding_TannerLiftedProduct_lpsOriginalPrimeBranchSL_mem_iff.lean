-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_mem_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:11.115562+00:00
-- url     : https://prove2.me/theorems/689fef60-d61a-4753-9088-a03c2f985807
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL mem iff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L139-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L139-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_mem_iff (p : ℕ) [Fact p.Prime]
    (i j : Option (Fin p)) :
    lpsOriginalPrimeBranchSL p i * (lpsOriginalPrimeBranchSL p j)⁻¹ ∈
      CongruenceSubgroup.Gamma0 p ↔ i=j := by sorry
