-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_mem
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:05.696971+00:00
-- url     : https://prove2.me/theorems/5ee4a079-08d7-4a62-9dc4-5679c85a7c9c
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Intersection mem
-- statement:
--   The second intersection has exactly its original level and integer upper-right divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L98-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L98-L102

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_mem (N p : ℕ) (γ : SL(2,ℤ)) :
    γ ∈ lpsHeckeConjugateIntersection N p ↔
      γ ∈ CongruenceSubgroup.Gamma0 N ∧ (p:ℤ) ∣ γ 0 1 := by sorry
