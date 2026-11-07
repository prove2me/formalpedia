-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_eq_zero_of_rightAmplitude_eq_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.eq_zero_of_rightAmplitude_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:31:32.076423+00:00
-- url     : https://prove2.me/theorems/6a279059-8433-4253-82eb-54c8bb62b9f3
-- title:
--   BPTCommuting Projector Model: eq zero of right Amplitude eq zero
-- statement:
--   Vanishing finite right amplitude has no hidden tensor component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L429-L441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L429-L441

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.eq_zero_of_rightAmplitude_eq_zero
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x : Semantics.CompositeSystem N C)
    (hamp : Semantics.DensityOperator.rightAmplitude b x = 0) :
    x = 0 := by sorry
