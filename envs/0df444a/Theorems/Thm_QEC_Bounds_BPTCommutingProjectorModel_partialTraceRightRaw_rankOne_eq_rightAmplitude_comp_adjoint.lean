-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint
-- name    : QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:29:16.878512+00:00
-- url     : https://prove2.me/theorems/607f647d-ab98-45cb-8e3f-37d1020a88fc
-- title:
--   BPTCommuting Projector Model: partial Trace Right Raw rank One eq right Amplitude comp adjoint
-- statement:
--   The right partial trace of a cross rank-one operator is its cross amplitude Gram operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L314-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L314-L331

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

theorem QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x y : Semantics.CompositeSystem N C) :
    Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (Semantics.DensityOperator.rightAmplitude b x).comp
        (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude b y)) := by sorry
