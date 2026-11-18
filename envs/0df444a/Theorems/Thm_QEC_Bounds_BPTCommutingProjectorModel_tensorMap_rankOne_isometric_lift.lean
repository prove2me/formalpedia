-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_rankOne_isometric_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_rankOne_isometric_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:13:18.610457+00:00
-- url     : https://prove2.me/theorems/2e02f28f-8856-4d57-b8a1-7a7e8d03a700
-- title:
--   BPTCommuting Projector Model: tensor Map rank One isometric lift
-- statement:
--   Tensoring a selected rank-one isometric lift with an arbitrary complement
--   operator is the corresponding joint isometric lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L356-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L356-L371

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_rankOne_isometric_lift
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (eSel : S →ₗ[Complex] H) (heSel : (LinearMap.adjoint eSel).comp eSel =
      (1 : Semantics.Operator S))
    (eComp : T →ₗ[Complex] K) (phi : S) (P : Semantics.Operator T) :
    TensorProduct.map (InnerProductSpace.rankOne Complex (eSel phi) (eSel phi)).toLinearMap
        (eComp.comp (P.comp (LinearMap.adjoint eComp))) =
      (TensorProduct.map eSel eComp).comp
        ((TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap P).comp
          (LinearMap.adjoint (TensorProduct.map eSel eComp))) := by sorry
