-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutActiveCoordinateTransport_intertwinesCore
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutActiveCoordinateTransport_intertwinesCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-17T23:57:56.443021+00:00
-- url     : https://prove2.me/theorems/e5d5596b-4e66-49e7-aa2c-33231c50cd96
-- title:
--   BPTCommuting Projector Model: second Cut Active Coordinate Transport intertwines Core
-- statement:
--   The selected middle action is the literal `N tensor X` coordinate action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/CoordinateTransport.lean#L33-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/CoordinateTransport.lean#L33-L129

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_CoordinateTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutActiveCoordinateTransport_intertwinesCore
    {A B C D W N X N2 : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    {pB : Submodule Complex B} {pC : Submodule Complex C}
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem X N2))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X)) :
    let T := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft A pB W N (Semantics.CompositeSystem pC D) UB)
      (composeUnitaryTransport
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (unitaryLTensor N
            (composeUnitaryTransport (unitaryRTensor UC D)
              (tensorAssociatorUnitary X N2 D))))
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))
    T.toLinearEquiv.toLinearMap.comp
        (jointBCSectorActiveUnitary (A := A) pB pC
          (activeSectorJointBCUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (unitaryRTensor U (Semantics.CompositeSystem N2 D))).toLinearEquiv.toLinearMap.comp
        T.toLinearEquiv.toLinearMap := by sorry
