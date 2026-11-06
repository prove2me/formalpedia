-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociator_right_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociator_right_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:37:56.20124+00:00
-- url     : https://prove2.me/theorems/b95b3822-0a57-4f7f-96e5-d779d6e620a1
-- title:
--   BPTCommuting Projector Model: tensor Associator right intertwines
-- statement:
--   Reassociation commutes with an operator on its final tensor factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L550-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L550-L574

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociator_right_intertwines
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J] (R : Semantics.Operator J) :
    (TensorProduct.map (1 : Semantics.Operator H)
      (TensorProduct.map (1 : Semantics.Operator K) R)).comp
        (tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap =
      (tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R) := by sorry
