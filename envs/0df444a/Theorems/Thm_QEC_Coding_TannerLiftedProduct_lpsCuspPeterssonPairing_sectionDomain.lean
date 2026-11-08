-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_sectionDomain
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_sectionDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:27.475092+00:00
-- url     : https://prove2.me/theorems/92411036-ef5b-4f94-8fb7-287cb2d35187
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing section Domain
-- statement:
--   The original convergent trace pairing is exactly the untraced integral on its genuine section domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L75-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L75-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_sectionDomain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f g =
      ∫τ in lpsCosetSectionDomain (lpsEffectiveGamma0 N) (lpsGamma0CosetSection N), petersson 2 f g τ := by sorry
