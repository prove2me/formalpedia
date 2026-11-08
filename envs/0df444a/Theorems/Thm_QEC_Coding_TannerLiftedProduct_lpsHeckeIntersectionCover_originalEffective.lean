-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCover_originalEffective
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_originalEffective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:59.349681+00:00
-- url     : https://prove2.me/theorems/e44db6b8-10c3-4605-a914-c07713881644
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Cover original Effective
-- statement:
--   The first genuine cover is a domain for the original effective Gamma0(Np).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L178-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L178-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_originalEffective (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveGamma0 (N*p))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by sorry
