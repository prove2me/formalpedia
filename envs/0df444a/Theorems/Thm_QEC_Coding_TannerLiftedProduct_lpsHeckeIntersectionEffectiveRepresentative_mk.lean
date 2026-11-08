-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionEffectiveRepresentative_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionEffectiveRepresentative_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:58:52.762849+00:00
-- url     : https://prove2.me/theorems/19f47a2d-fe56-4e4b-b537-9016371a8ce8
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Effective Representative mk
-- statement:
--   The projected first representatives satisfy the genuine effective section law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L68-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L68-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionEffectiveRepresentative_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeIntersectionEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm i := by sorry
