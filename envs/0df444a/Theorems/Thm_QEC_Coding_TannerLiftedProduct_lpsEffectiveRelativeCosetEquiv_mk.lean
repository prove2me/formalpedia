-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveRelativeCosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveRelativeCosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:08.927955+00:00
-- url     : https://prove2.me/theorems/059661e1-947d-455b-aaa1-90e51b9526ba
-- title:
--   Tanner Lifted Product: lps Effective Relative Coset Equiv mk
-- statement:
--   The genuine relative quotient transport evaluates by the original effective projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveRelativeCosets.lean#L58-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveRelativeCosets.lean#L58-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveRelativeCosetEquiv_mk (N : ℕ) (H : Subgroup SL(2,ℤ))
    (hker : (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ H)
    (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveRelativeCosetEquiv N H hker (QuotientGroup.mk γ) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ) := by sorry
