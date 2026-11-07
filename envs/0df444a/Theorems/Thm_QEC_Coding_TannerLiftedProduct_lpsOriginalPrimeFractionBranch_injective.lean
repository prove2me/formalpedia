-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeFractionBranch_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeFractionBranch_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:30:13.407658+00:00
-- url     : https://prove2.me/theorems/2be8f39e-42ce-4a6f-8e2a-c8bb1aea57f4
-- title:
--   Tanner Lifted Product: lps Original Prime Fraction Branch injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Fraction Branch injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L220-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L220-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeFractionBranch_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalPrimeFractionBranch p) := by sorry
