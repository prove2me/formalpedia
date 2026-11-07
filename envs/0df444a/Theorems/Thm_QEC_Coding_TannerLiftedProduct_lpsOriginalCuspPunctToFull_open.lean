-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctToFull_open
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:58.558581+00:00
-- url     : https://prove2.me/theorems/4c2b9aa6-1bbe-4261-a0e8-8e182d5ed5f3
-- title:
--   Tanner Lifted Product: lps Original Cusp Punct To Full open
-- statement:
--   The actual punctured-to-full disc inclusion is open.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L269-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L269-L275

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctToFull_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctToFull N ρ) := by sorry
