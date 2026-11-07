-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:30:07.468729+00:00
-- url     : https://prove2.me/theorems/284feff6-ee43-4b6a-970d-ada7d766a2fe
-- title:
--   BPTCommuting Projector Model: adjoint comp eq of partial Trace Left Raw rank One self eq
-- statement:
--   The transpose convention for the left raw marginal still identifies the right Gram operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L334-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L334-L379

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (bN : OrthonormalBasis (Fin (Module.finrank Complex N)) Complex N)
    (bC : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x y : Semantics.CompositeSystem N C)
    (hnormx : ‖x‖ ^ 2 = 1) (hnormy : ‖y‖ ^ 2 = 1)
    (hraw : Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x x).toLinearMap =
      Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex y y).toLinearMap) :
    (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude bC x)).comp
        (Semantics.DensityOperator.rightAmplitude bC x) =
      (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude bC y)).comp
        (Semantics.DensityOperator.rightAmplitude bC y) := by sorry
