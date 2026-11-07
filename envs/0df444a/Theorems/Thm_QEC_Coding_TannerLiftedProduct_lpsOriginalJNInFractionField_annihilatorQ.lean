-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilatorQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilatorQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:02:23.932209+00:00
-- url     : https://prove2.me/theorems/e1b50435-d0ed-40f8-8958-4f127e127bf6
-- title:
--   Tanner Lifted Product: lps Original JNIn Fraction Field annihilator Q
-- statement:
--   Actual mapped monic annihilator of SAME original jN with the genuine finite coset-card upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L104-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L104-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilatorQ (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∃ P : Polynomial (FractionRing (Polynomial ℚ)), P.Monic ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P=0 := by sorry
