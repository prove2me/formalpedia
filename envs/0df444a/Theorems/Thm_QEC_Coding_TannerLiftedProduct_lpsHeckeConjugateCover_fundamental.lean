-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateCover_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:00:23.314501+00:00
-- url     : https://prove2.me/theorems/6ea6184d-403e-4749-a800-6827ef94bf30
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Cover fundamental
-- statement:
--   The actual second inverse-section cover is an effective relative-intersection domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L169-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L169-L175

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCover_fundamental (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by sorry
