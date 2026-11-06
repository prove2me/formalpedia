-- Prove2me | Theorems.Thm_QEC_Bounds_tensorAssociator_symm_right_intertwines
-- name    : QEC.Bounds.tensorAssociator_symm_right_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:31.867182+00:00
-- url     : https://prove2.me/theorems/eb500d32-d929-4162-a27b-71286b409eb7
-- title:
--   Bounds: tensor Associator symm right intertwines
-- statement:
--   Moving a final-factor operator through the inverse tensor associator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/TensorCoordinates.lean#L22-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/TensorCoordinates.lean#L22-L45

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_TensorCoordinates
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 50000

theorem QEC.Bounds.tensorAssociator_symm_right_intertwines
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J] (R : Semantics.Operator J) :
    (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R).comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.toLinearEquiv.toLinearMap =
      (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (1 : Semantics.Operator H)
          (TensorProduct.map (1 : Semantics.Operator K) R)) := by sorry
