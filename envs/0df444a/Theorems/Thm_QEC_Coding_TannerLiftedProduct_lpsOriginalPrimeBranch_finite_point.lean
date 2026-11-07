-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranch_finite_point
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_finite_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:33.987755+00:00
-- url     : https://prove2.me/theorems/ebbce00a-9d1a-473e-b59b-0b470200e734
-- title:
--   Tanner Lifted Product: lps Original Prime Branch finite point
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch finite point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L62-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_finite_point (p : ℕ) [Fact p.Prime] (m : Fin p) (τ : ℍ) :
    ((lpsHeckeUpperGL ℝ p (some m) • τ:ℍ):ℂ)=
      ((τ:ℂ)+(m.val:ℂ))/(p:ℂ) := by sorry
