-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_covers
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:16.851343+00:00
-- url     : https://prove2.me/theorems/ee2e05db-f1f3-4798-ae30-be3acdf4265d
-- title:
--   Tanner Lifted Product: lps Coset Section Domain covers
-- statement:
--   A genuine coset section gives actual subgroup orbit coverage, including infinite index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L29-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L29-L43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_covers (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) (hr : ∀c, QuotientGroup.mk (r c) = c) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCosetSectionDomain H r := by sorry
