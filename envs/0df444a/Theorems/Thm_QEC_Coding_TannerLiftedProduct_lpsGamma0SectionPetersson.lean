-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0SectionPetersson
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0SectionPetersson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:25.857818+00:00
-- url     : https://prove2.me/theorems/52588866-2b5c-4234-9f13-a1b85b0fcac9
-- title:
--   Tanner Lifted Product: lps Gamma0 Section Petersson
-- statement:
--   A projected inverse-section integrand is the original Gamma0 coset Petersson component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L35-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L35-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0SectionPetersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) =
      lpsCuspCosetPetersson N f g τ ((lpsEffectiveGamma0CosetEquiv N).symm c) := by sorry
