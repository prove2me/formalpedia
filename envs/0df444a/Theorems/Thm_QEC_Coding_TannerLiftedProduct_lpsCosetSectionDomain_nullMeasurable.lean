-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_nullMeasurable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_nullMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:12.487365+00:00
-- url     : https://prove2.me/theorems/bf38d0b1-f23a-4dfb-aa6f-64b7f05bceba
-- title:
--   Tanner Lifted Product: lps Coset Section Domain null Measurable
-- statement:
--   Every inverse-section union is null measurable for actual hyperbolic volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L20-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L20-L26

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_nullMeasurable (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCosetSectionDomain H r) volume := by sorry
