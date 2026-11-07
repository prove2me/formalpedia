-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_finite_dilation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_dilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:29:22.199932+00:00
-- url     : https://prove2.me/theorems/f4afb856-ebe7-4a9d-8727-ba7f3d78a632
-- title:
--   Tanner Lifted Product: lps Original Prime Branch SL finite dilation
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch SL finite dilation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L86-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L86-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchSL_finite_dilation (p : ℕ) [Fact p.Prime]
    (m : Fin p) (τ : ℍ) :
    lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 •
      (lpsOriginalPrimeBranchSL p (some m) • τ)=
      ModularGroup.S • (lpsHeckeUpperGL ℝ p (some m) • τ) := by sorry
