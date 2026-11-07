-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_cusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:03.462195+00:00
-- url     : https://prove2.me/theorems/61974d0b-d425-4b00-a8fa-990089fcbccb
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Chart cusp
-- statement:
--   The selected genuine cusp is the zero of its actual filled chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L67-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L67-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    lpsOriginalFilledCuspChart N c (Sum.inr c)=0 := by sorry
