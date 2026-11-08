-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSubgroup_perm
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveSubgroup_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:35.925912+00:00
-- url     : https://prove2.me/theorems/6a17e9e2-4934-480b-83c6-d1900f2e2e30
-- title:
--   Tanner Lifted Product: lps Effective Subgroup perm
-- statement:
--   Effective projection followed by subtype gives the original permutation image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L65-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L65-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveSubgroup_perm (H : Subgroup SL(2,ℤ)) :
    (H.map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict).map
      lpsEffectiveModularGroup.subtype=H.map (MulAction.toPermHom SL(2,ℤ) ℍ) := by sorry
