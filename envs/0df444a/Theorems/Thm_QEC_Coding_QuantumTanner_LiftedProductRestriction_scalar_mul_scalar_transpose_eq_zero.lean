-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_scalar_mul_scalar_transpose_eq_zero
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.scalar_mul_scalar_transpose_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:56.895712+00:00
-- url     : https://prove2.me/theorems/a11968ed-23ba-463b-85a7-21b94f39a604
-- title:
--   Lifted Product Restriction: scalar mul scalar transpose eq zero
-- statement:
--   The untwisted scalar embedding preserves a raw dual-check cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L137-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L137-L141

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
noncomputable section
variable {F G I J K : Type*} [CommRing F] [Group G] [Fintype K]

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.scalar_mul_scalar_transpose_eq_zero
    (h : Matrix I K F) (g : Matrix J K F) (hzero : h * g.transpose = 0) :
    scalarMatrix (G := G) h * (scalarMatrix (G := G) g).transpose = 0 := by sorry
