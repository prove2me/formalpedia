-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_volume
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:39.820573+00:00
-- url     : https://prove2.me/theorems/5fa17ee3-386f-4720-b60c-440ad342171f
-- title:
--   Tanner Lifted Product: lps Coset Section Domain volume
-- statement:
--   The true finite-cover volume is exact subgroup index times modular-domain volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L112-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L112-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_volume (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    (volume : Measure ℍ) (lpsCosetSectionDomain H r) =
      (H.index : ℝ≥0∞) * volume ModularGroup.fd := by sorry
