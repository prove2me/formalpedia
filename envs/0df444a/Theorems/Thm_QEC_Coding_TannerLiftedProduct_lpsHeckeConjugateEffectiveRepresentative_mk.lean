-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateEffectiveRepresentative_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateEffectiveRepresentative_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:58:57.428267+00:00
-- url     : https://prove2.me/theorems/a5113331-4c40-4b2c-8b4a-c9a4ce9e835c
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Effective Representative mk
-- statement:
--   The projected second representatives satisfy the actual effective section law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L152-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L152-L165

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateEffectiveRepresentative_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeConjugateEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm i := by sorry
