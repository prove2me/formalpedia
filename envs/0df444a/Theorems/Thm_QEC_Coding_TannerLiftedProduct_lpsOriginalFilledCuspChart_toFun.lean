-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_toFun
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_toFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:12.291167+00:00
-- url     : https://prove2.me/theorems/5523ec39-fed2-44cb-8b68-8750d4f6d279
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Chart to Fun
-- statement:
--   The true filled chart retains exactly the previously constructed original q-coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L60-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L60-L64

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_toFun (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledCuspChart N c : LPSOriginalFilledCurve N → ℂ)=
      lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c) := by sorry
