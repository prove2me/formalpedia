-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_twisted_mul_inverse_twisted_transpose
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:46.124196+00:00
-- url     : https://prove2.me/theorems/233d0cdd-9510-41ea-8717-aa5462d4ee2f
-- title:
--   Lifted Product Restriction: twisted mul inverse twisted transpose
-- statement:
--   Opposite column twists cancel in their original order, without assuming G abelian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L117-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L117-L125

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

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.twisted_mul_inverse_twisted_transpose
    (h : Matrix I K F) (g : Matrix J K F) (s : K → G) :
    twistedMatrix h s * (twistedMatrix g (fun k => (s k)⁻¹)).transpose =
      scalarMatrix (G := G) (h * g.transpose) := by sorry
