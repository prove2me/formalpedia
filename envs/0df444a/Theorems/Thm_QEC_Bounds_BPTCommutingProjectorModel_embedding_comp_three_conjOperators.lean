-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_embedding_comp_three_conjOperators
-- name    : QEC.Bounds.BPTCommutingProjectorModel.embedding_comp_three_conjOperators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:12.806236+00:00
-- url     : https://prove2.me/theorems/3f45702b-efe5-4840-8483-a0958cc7be58
-- title:
--   BPTCommuting Projector Model: embedding comp three conj Operators
-- statement:
--   Three unitary coordinate changes followed by an embedding preserve an operator lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransportBasic.lean#L46-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransportBasic.lean#L46-L87

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportBasic
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.embedding_comp_three_conjOperators
    {A B C D E : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    (U : Semantics.UnitaryTransport A B)
    (V : Semantics.UnitaryTransport B C)
    (W : Semantics.UnitaryTransport C D)
    (J : D →ₗ[Complex] E) (P : Semantics.Operator A) :
    J.comp ((W.conjOperator (V.conjOperator (U.conjOperator P))).comp
      (LinearMap.adjoint J)) =
      (J.comp (W.toLinearEquiv.toLinearMap.comp
        (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap))).comp
        (P.comp (LinearMap.adjoint
          (J.comp (W.toLinearEquiv.toLinearMap.comp
            (V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap))))) := by sorry
