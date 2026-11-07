-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCurve_finite_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCurve_finite_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:47.772466+00:00
-- url     : https://prove2.me/theorems/52db916c-094b-48a4-9d72-cbe52959a1dd
-- title:
--   Tanner Lifted Product: lps Original Filled Curve finite cover
-- statement:
--   The actual compact core and finitely many true closed cusp patches cover the ENTIRE filled set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L225-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L225-L249

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCurve_finite_cover (N : ℕ) [NeZero N] :
    (Sum.inl '' lpsOriginalGamma0CompactCore N 2) ∪
      (⋃ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        lpsOriginalFilledCuspClosedPatch N c)=Set.univ := by sorry
