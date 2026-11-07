-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_compactSpace
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_compactSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:56.453016+00:00
-- url     : https://prove2.me/theorems/0c86232a-5102-4ebb-9d50-da61bb2eb31f
-- title:
--   Tanner Lifted Product: lps Original Filled Topology compact Space
-- statement:
--   The whole actual filled topology is compact by the genuine finite compact cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L75-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L75-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_compactSpace (N : ℕ) [NeZero N] :
    @CompactSpace (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by sorry
