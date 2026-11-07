-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0OneTop
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0OneTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:43.400587+00:00
-- url     : https://prove2.me/theorems/77d5b857-bede-495b-9fa9-65f8a8bc4f96
-- title:
--   Tanner Lifted Product: lps Original Gamma0 One Top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gamma0 One Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L31-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L31-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0OneTop : CongruenceSubgroup.Gamma0 1=⊤ := by sorry
