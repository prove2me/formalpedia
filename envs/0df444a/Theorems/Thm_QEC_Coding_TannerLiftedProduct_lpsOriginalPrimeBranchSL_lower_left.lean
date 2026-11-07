-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_lower_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_lower_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:28:16.057605+00:00
-- url     : https://prove2.me/theorems/1e5a543c-c85c-4a8a-afa3-4059aebf1bba
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL lower left
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL lower left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L127-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L127-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_lower_left (p : ℕ) (i j : Option (Fin p)) :
    (lpsOriginalPrimeBranchSL p i * (lpsOriginalPrimeBranchSL p j)⁻¹) 1 0=
      match i,j with
      | none,none => 0
      | none,some _ => -1
      | some _,none => 1
      | some m,some n => (n.val:ℤ)-(m.val:ℤ) := by sorry
