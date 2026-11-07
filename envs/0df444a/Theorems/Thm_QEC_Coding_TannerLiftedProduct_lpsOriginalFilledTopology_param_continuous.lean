-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:04.834937+00:00
-- url     : https://prove2.me/theorems/03cbe9da-d7c6-4f1c-acc7-12d731738c2e
-- title:
--   Tanner Lifted Product: lps Original Filled Topology param continuous
-- statement:
--   The genuine filled-disc parametrization is continuous for the specified gluing topology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L53-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L53-L59

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_continuous (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by sorry
