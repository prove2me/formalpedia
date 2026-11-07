-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_t2Space
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_t2Space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:43:06.877308+00:00
-- url     : https://prove2.me/theorems/bd544b5c-79d8-4086-bab6-f0f33050fef8
-- title:
--   Tanner Lifted Product: lps Original Filled Topology t2 Space
-- statement:
--   The actual filled topology is Hausdorff, including interior-cusp and cusp-cusp separation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L202-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L202-L242

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_t2Space (N : ℕ) [NeZero N] :
    @T2Space (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by sorry
