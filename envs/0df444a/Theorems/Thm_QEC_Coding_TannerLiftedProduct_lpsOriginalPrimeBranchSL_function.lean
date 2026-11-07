-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_function
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_function
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:13.611212+00:00
-- url     : https://prove2.me/theorems/796acebd-011c-4f5f-a8aa-3fa3d83b13f6
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL function
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L101-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L101-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_function (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    lpsOriginalJDilated p (Fact.out : p.Prime).pos
      (lpsOriginalPrimeBranchSL p i • τ)=lpsOriginalPrimeBranch p i τ := by sorry
