-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_twisted_mul_inverse_twisted_transpose_eq_zero
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:39.811563+00:00
-- url     : https://prove2.me/theorems/018313f8-1f18-46d0-bcb2-509bb9bb16cc
-- title:
--   Lifted Product Restriction: twisted mul inverse twisted transpose eq zero
-- statement:
--   A raw scalar orthogonality identity implies the corresponding twisted cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L128-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L128-L134

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

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose_eq_zero
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G)
    (hzero : h * g.transpose = 0) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose = 0 := by sorry
