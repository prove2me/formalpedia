-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_finite_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:28:38.016281+00:00
-- url     : https://prove2.me/theorems/17dbb3f3-0387-4f16-9cc5-17f268eedb0e
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL finite coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL finite coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L80-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L80-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_coe (p : ℕ) (m : Fin p) (τ : ℍ) :
    ((lpsOriginalPrimeBranchSL p (some m) • τ : ℍ) : ℂ)=
      -1/((τ:ℂ)+(m.val:ℂ)) := by sorry
