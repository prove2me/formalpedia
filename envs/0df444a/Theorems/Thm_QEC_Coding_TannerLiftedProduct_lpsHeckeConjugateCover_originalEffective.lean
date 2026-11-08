-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateCover_originalEffective
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_originalEffective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:57.631186+00:00
-- url     : https://prove2.me/theorems/22220d35-61a6-449a-b712-2bfd18181998
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Cover original Effective
-- statement:
--   The second genuine cover is a domain for the actual effective upper-right intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L188-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L188-L195

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_originalEffective (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by sorry
