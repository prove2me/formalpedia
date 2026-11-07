-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_annihilator
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:32.770077+00:00
-- url     : https://prove2.me/theorems/65a3b118-85bd-4bc8-b2ab-a154af764cfa
-- title:
--   Tanner Lifted Product: lps Original JNIn Fraction Field annihilator
-- statement:
--   Actual mapped monic annihilator of SAME original jN, bounded by the true coset cardinal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L143-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L143-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_annihilator (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P=0 := by sorry
