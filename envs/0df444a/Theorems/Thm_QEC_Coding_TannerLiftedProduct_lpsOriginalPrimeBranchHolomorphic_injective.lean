-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchHolomorphic_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:29:40.980495+00:00
-- url     : https://prove2.me/theorems/b66a8a5b-dccd-4e1c-acbd-167df07b02d9
-- title:
--   Tanner Lifted Product: lps Original Prime Branch Holomorphic injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Branch Holomorphic injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L160-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L160-L174

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranchHolomorphic_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalPrimeBranchHolomorphic p) := by sorry
