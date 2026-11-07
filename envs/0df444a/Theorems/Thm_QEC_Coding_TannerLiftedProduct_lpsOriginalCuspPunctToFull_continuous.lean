-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctToFull_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:00.929517+00:00
-- url     : https://prove2.me/theorems/b74c0453-afe3-4ed7-9058-2d514112fda4
-- title:
--   Tanner Lifted Product: lps Original Cusp Punct To Full continuous
-- statement:
--   The actual punctured-to-full disc inclusion is continuous.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L264-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L264-L266

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_continuous (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Continuous (lpsOriginalCuspPunctToFull N ρ) := by sorry
