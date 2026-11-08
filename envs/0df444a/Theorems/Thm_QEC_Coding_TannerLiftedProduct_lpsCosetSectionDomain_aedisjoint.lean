-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_aedisjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_aedisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:18.154074+00:00
-- url     : https://prove2.me/theorems/e0c87970-95cf-4943-8bad-3c98e392b86f
-- title:
--   Tanner Lifted Product: lps Coset Section Domain aedisjoint
-- statement:
--   Distinct subgroup translates of a genuine inverse-section union are almost disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L46-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L46-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_aedisjoint (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCosetSectionDomain H r) (lpsCosetSectionDomain H r) := by sorry
