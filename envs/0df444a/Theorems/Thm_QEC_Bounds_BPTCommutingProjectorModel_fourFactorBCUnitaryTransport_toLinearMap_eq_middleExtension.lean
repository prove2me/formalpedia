-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:43.878929+00:00
-- url     : https://prove2.me/theorems/f3e2373e-213b-42bb-a92f-ee5b07e8f2e2
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport to Linear Map eq middle Extension
-- statement:
--   The four-factor BC unitary transport has the literal `R† (1 tensor E tensor
--   1) R` operator as its linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L138-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L138-L151

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C)) :
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map E.toLinearEquiv.toLinearMap
            (1 : Semantics.Operator D))) := by sorry
