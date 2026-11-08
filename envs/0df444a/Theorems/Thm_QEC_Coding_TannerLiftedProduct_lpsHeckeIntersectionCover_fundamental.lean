-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCover_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:07.365925+00:00
-- url     : https://prove2.me/theorems/5e47d296-9016-4dc3-b450-c04e164665e9
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Cover fundamental
-- statement:
--   The original first inverse-section cover is a true effective relative-intersection domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L85-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L85-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCover_fundamental (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by sorry
