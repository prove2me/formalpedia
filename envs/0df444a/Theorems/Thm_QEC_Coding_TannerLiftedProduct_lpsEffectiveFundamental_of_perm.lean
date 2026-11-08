-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamental_of_perm
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_of_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:00.881654+00:00
-- url     : https://prove2.me/theorems/bee20ebe-9e73-4789-bbb8-3d0641b11052
-- title:
--   Tanner Lifted Product: lps Effective Fundamental of perm
-- statement:
--   Pull a true permutation-image domain back along the injective effective action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L99-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L99-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_of_perm (H : Subgroup lpsEffectiveModularGroup)
    {s : Set ℍ} (hs : IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume) :
    IsFundamentalDomain H s volume := by sorry
