-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:52:36.563195+00:00
-- url     : https://prove2.me/theorems/24e15e66-88cb-4f90-abba-2821232b2537
-- title:
--   Tanner Lifted Product: lps Coset Section Domain integral
-- statement:
--   Integrable components give the true finite-cover integral, with inverse action orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L95-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCosetSectionDomain.lean#L95-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_integral (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (F : ℍ → ℂ)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • ModularGroup.fd) volume) :
    (∫τ in lpsCosetSectionDomain H r, F τ) =
      ∑' c, ∫τ in ModularGroup.fd, F ((r c)⁻¹ • τ) := by sorry
