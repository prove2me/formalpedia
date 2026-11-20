-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociator_symm_conj_rankOneTensor
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociator_symm_conj_rankOneTensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:10.852044+00:00
-- url     : https://prove2.me/theorems/7b85199c-43a0-42a6-802e-c2be24b15cd9
-- title:
--   BPTCommuting Projector Model: tensor Associator symm conj rank One Tensor
-- statement:
--   Reassociating a rank-one selected factor and a rank-one boundary factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L301-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L301-L314

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociator_symm_conj_rankOneTensor
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J]
    (phi : H) (chi : K) (Q : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).symm.conjOperator
      (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
          (phi ⊗ₜ[Complex] chi)).toLinearMap Q := by sorry
