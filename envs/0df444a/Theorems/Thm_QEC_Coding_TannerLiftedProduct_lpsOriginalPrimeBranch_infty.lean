-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranch_infty
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_infty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:17:35.091349+00:00
-- url     : https://prove2.me/theorems/f7a9d355-553a-415b-b010-a1d3cd0f4aec
-- title:
--   Tanner Lifted Product: lps Original Prime Branch infty
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L57-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_infty (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    lpsOriginalPrimeBranch p none τ=lpsOriginalJDilated p (Fact.out : p.Prime).pos τ := by sorry
