-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_selected_groupAlgebra_auxiliary_disjoint
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_groupAlgebra_auxiliary_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:08:27.542202+00:00
-- url     : https://prove2.me/theorems/8b50241e-2fc0-4d68-b226-e0a6a6f0da24
-- title:
--   Lifted Product Restriction: selected group Algebra auxiliary disjoint
-- statement:
--   Instantiate the auxiliary-support separation from raw local dual checks.
--   The only zero-product inputs are the two scalar dual-check identities in
--   [LZDec22, Section "Quantum Tanner codes from Lifted Product codes"].
--   All twisted group-algebra cancellations are derived, not supplied as data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L148-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L148-L170

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
omit [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_groupAlgebra_auxiliary_disjoint
    (hA : Matrix C A F) (hB : Matrix D B F)
    (gA : Matrix C' A F) (gB : Matrix D' B F)
    (a : A → G) (b : B → G)
    (hDualA : gA * hA.transpose = 0) (hDualB : gB * hB.transpose = 0)
    (U0 U1 : Matrix C D' (MonoidAlgebra F G))
    (V0 V1 : Matrix C' D (MonoidAlgebra F G))
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary (scalarMatrix hB) (twistedMatrix hB b)
        (U0 * twistedMatrix gB (fun k => (b k)⁻¹)) (U1 * scalarMatrix gB) c d = 0 ∨
      xAuxiliary (scalarMatrix hA) (twistedMatrix hA a)
        ((scalarMatrix gA).transpose * V0)
        ((twistedMatrix gA (fun k => (a k)⁻¹)).transpose * V1) c d = 0 := by sorry
