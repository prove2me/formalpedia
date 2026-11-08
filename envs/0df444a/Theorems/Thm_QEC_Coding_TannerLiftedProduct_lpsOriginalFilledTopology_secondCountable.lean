-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_secondCountable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_secondCountable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:37.455282+00:00
-- url     : https://prove2.me/theorems/efb94d67-111b-4e1a-b2ff-b081efe9ed09
-- title:
--   Tanner Lifted Product: lps Original Filled Topology second Countable
-- statement:
--   The actual filled topology is second countable via its genuine open surjective finite-disc cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L245-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L245-L271

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_secondCountable (N : ℕ) [NeZero N] :
    @SecondCountableTopology (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N) := by sorry
