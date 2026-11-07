-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0CompactCore_isCompact
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0CompactCore_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:02.158072+00:00
-- url     : https://prove2.me/theorems/535ee95f-5f87-407f-a80a-8c4d3b6fe8ce
-- title:
--   Tanner Lifted Product: lps Original Gamma0 Compact Core is Compact
-- statement:
--   The genuine truncated core is compact by finite index and continuous images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L43-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L43-L48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0CompactCore_isCompact (N : ℕ) [NeZero N] (Y : ℝ) :
    IsCompact (lpsOriginalGamma0CompactCore N Y) := by sorry
