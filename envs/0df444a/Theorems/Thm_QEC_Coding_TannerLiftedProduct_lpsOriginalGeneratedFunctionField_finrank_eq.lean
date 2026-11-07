-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:04:45.749237+00:00
-- url     : https://prove2.me/theorems/9296ccb4-2212-4d12-b054-a37eabe65198
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field finrank eq
-- statement:
--   The exact degree of SAME generated original C(j,jN) equals actual Gamma0 coset cardinal, by true distinct minpoly roots and the proved upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L178-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L178-L212

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_eq (N : ℕ) [NeZero N]
    (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
