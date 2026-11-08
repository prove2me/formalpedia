-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveHeckeIntersectionCosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeIntersectionCosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:58:27.076233+00:00
-- url     : https://prove2.me/theorems/92cf0e35-11ec-459a-9235-10013f319b8d
-- title:
--   Tanner Lifted Product: lps Effective Hecke Intersection Coset Equiv mk
-- statement:
--   The first effective coset equivalence agrees with original relative coset evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L24-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L24-L39

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeIntersectionCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeIntersectionCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) := by sorry
