-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchHolomorphic_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:34.535231+00:00
-- url     : https://prove2.me/theorems/0e6d6781-ce39-4c11-8c12-2209fd0dea28
-- title:
--   Tanner Lifted Product: lps Original Prime Branch Holomorphic apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch Holomorphic apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L119-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L119-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_apply (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalPrimeBranchHolomorphic p i).val τ=lpsOriginalPrimeBranch p i τ := by sorry
