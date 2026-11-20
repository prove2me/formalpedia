-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rankOneTensor_sourceFactorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rankOneTensor_sourceFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:42.427803+00:00
-- url     : https://prove2.me/theorems/a6817134-dd7f-4f0a-9c2e-f608fe82939f
-- title:
--   BPTCommuting Projector Model: rank One Tensor source Factorization
-- statement:
--   The source rank-one sandwich calculation in two concrete tensor factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L42-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L42-L101

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rankOneTensor_sourceFactorization
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (A : Semantics.Operator H) (B : Semantics.Operator K) :
    let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    let codeProjector := TensorProduct.map rankOne Q
    codeProjector * TensorProduct.map A (1 : Semantics.Operator K) *
        TensorProduct.map (1 : Semantics.Operator H) B * codeProjector =
      (inner Complex phi (A phi)) •
        (codeProjector * TensorProduct.map (1 : Semantics.Operator H) B *
          codeProjector) := by sorry
