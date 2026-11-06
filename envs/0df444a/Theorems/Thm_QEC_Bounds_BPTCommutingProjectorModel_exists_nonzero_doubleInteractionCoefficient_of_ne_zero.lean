-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_nonzero_doubleInteractionCoefficient_of_ne_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_nonzero_doubleInteractionCoefficient_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:11.675383+00:00
-- url     : https://prove2.me/theorems/4eb22cd4-4afe-4823-be04-0cc271717214
-- title:
--   BPTCommuting Projector Model: exists nonzero double Interaction Coefficient of ne zero
-- statement:
--   A nonzero triple-overlap operator has a nonzero double interaction coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4111-L4129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4111-L4129

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_nonzero_doubleInteractionCoefficient_of_ne_zero
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (T : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C))
    (hT : T ≠ 0) :
    ∃ c c' : C, ∃ a a' : A,
      leftInteractionCoefficient (rightInteractionCoefficient T c c') a a' ≠ 0 := by sorry
