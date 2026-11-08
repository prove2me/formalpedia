-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_sectionSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_sectionSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:22.202815+00:00
-- url     : https://prove2.me/theorems/66d15018-a9f9-4f98-94a2-c580c0d4a202
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace section Sum
-- statement:
--   The actual original Petersson trace reindexes over effective Gamma0 cosets, without a center factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L59-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L59-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_sectionSum (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonTrace N f g τ =
      ∑' c, petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) := by sorry
