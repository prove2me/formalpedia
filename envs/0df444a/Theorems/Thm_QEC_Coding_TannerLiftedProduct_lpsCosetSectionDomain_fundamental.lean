-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:16.441204+00:00
-- url     : https://prove2.me/theorems/6b70cbf2-21da-42df-8ca5-31d2a05b3a6b
-- title:
--   Tanner Lifted Product: lps Coset Section Domain fundamental
-- statement:
--   Every genuine coset section constructs an actual subgroup fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L70-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L70-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_fundamental (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    IsFundamentalDomain H (lpsCosetSectionDomain H r) volume := by sorry
