-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_components
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:51:48.101973+00:00
-- url     : https://prove2.me/theorems/66fecd16-c979-4701-8aac-f03147e2a101
-- title:
--   Tanner Lifted Product: lps Coset Section Domain components
-- statement:
--   Distinct genuine inverse-coset components are almost disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L81-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L81-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_components (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    Pairwise (fun c d => AEDisjoint volume ((r c)⁻¹ • ModularGroup.fd)
      ((r d)⁻¹ • ModularGroup.fd)) := by sorry
