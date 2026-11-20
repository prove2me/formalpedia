-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rankOne_sandwich
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rankOne_sandwich
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:28.750396+00:00
-- url     : https://prove2.me/theorems/b6c07bb4-db22-446f-a859-10f658b3a050
-- title:
--   BPTCommuting Projector Model: rank One sandwich
-- statement:
--   Sandwiching an operator by a normalized rank-one projector is scalar on that line.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L25-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L25-L39

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rankOne_sandwich
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (phi : H) (hphi : ‖phi‖ = 1) (A : Semantics.Operator H) :
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap * A *
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap =
      (inner Complex phi (A phi)) •
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by sorry
