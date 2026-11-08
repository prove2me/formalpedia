-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamental_perm
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:00:43.362653+00:00
-- url     : https://prove2.me/theorems/ace346ec-2736-4e2f-a139-8671f7708976
-- title:
--   Tanner Lifted Product: lps Effective Fundamental perm
-- statement:
--   A true effective-subgroup domain transports to its injective permutation image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L16-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L16-L21

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_perm (H : Subgroup lpsEffectiveModularGroup)
    {s : Set ℍ} (hs : IsFundamentalDomain H s volume) :
    IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume := by sorry
