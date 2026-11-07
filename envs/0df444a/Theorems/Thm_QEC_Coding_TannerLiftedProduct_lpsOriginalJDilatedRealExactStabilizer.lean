-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedRealExactStabilizer
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedRealExactStabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:10:57.130205+00:00
-- url     : https://prove2.me/theorems/da62748e-ee64-4cba-8581-c1040f519120
-- title:
--   Tanner Lifted Product: lps Original JDilated Real Exact Stabilizer
-- statement:
--   The proved integral exact stabilizer identifies the actual real SL-range stabilizer with the SAME real Gamma0 subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L125-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L125-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedRealExactStabilizer (N : ℕ) (hN : 0<N)
    (g : 𝒮ℒ) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (g.val•τ)=lpsOriginalJDilated N hN τ)↔
      g.val∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by sorry
