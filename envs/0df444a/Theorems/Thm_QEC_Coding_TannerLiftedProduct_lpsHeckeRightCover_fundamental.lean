-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightCover_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightCover_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:45.198414+00:00
-- url     : https://prove2.me/theorems/98547f0d-c82c-4eec-968e-43fa6b8d6704
-- title:
--   Tanner Lifted Product: lps Hecke Right Cover fundamental
-- statement:
--   The second cover is a genuine domain for the same effective upper-right intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L124-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L124-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightCover_fundamental (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by sorry
