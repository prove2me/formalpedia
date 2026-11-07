-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_source
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:02.782047+00:00
-- url     : https://prove2.me/theorems/b0c19e4e-6f19-4621-ac03-8ece7b7767c9
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Chart source
-- statement:
--   The full chart source is exactly the original punctured neighborhood plus its genuine cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L77-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L77-L81

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_source (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledCuspChart N c).source=
      lpsOriginalFilledCuspSource N (lpsOriginalCuspRepresentative N c) := by sorry
