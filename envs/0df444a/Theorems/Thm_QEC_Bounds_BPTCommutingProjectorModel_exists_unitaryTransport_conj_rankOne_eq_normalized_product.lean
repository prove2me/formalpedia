-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_unitaryTransport_conj_rankOne_eq_normalized_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_unitaryTransport_conj_rankOne_eq_normalized_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:32:25.720658+00:00
-- url     : https://prove2.me/theorems/b5b233de-6f3b-43f8-94e5-e536d71dd394
-- title:
--   BPTCommuting Projector Model: exists unitary Transport conj rank One eq normalized product
-- statement:
--   The D1 global unitary sends the corresponding pure rank-one operator to a product rank one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductUnitary.lean#L123-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ProductUnitary.lean#L123-L136

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_unitaryTransport_conj_rankOne_eq_normalized_product
    {N C : Type u} [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (psi : Semantics.CompositeSystem N C) (hpsi : ‖psi‖ = 1) :
    ∃ n0 : N, ∃ c0 : C, ‖n0‖ = 1 ∧ ‖c0‖ = 1 ∧
      ∃ U : Semantics.UnitaryTransport (Semantics.CompositeSystem N C)
        (Semantics.CompositeSystem N C), U psi = n0 ⊗ₜ[Complex] c0 ∧
        U.conjOperator (InnerProductSpace.rankOne Complex psi psi).toLinearMap =
          (InnerProductSpace.rankOne Complex (n0 ⊗ₜ[Complex] c0)
            (n0 ⊗ₜ[Complex] c0)).toLinearMap := by sorry
