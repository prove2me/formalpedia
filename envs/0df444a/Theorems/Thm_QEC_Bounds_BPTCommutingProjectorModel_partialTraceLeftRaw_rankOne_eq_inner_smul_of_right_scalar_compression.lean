-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceLeftRaw_rankOne_eq_inner_smul_of_right_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.partialTraceLeftRaw_rankOne_eq_inner_smul_of_right_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:31:13.690919+00:00
-- url     : https://prove2.me/theorems/0e27ff84-8a5e-47b1-8f61-ad964eedf255
-- title:
--   BPTCommuting Projector Model: partial Trace Left Raw rank One eq inner smul of right scalar compression
-- statement:
--   The factor-swapped companion of
--   `partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression`.
--   Right-factor scalar compression kills cross terms after tracing out the left
--   factor, without asserting any scalarity for joint observables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L126-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L126-L214

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

theorem QEC.Bounds.BPTCommutingProjectorModel.partialTraceLeftRaw_rankOne_eq_inner_smul_of_right_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y) (hnorm : inner Complex x x = 1) :
    Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap := by sorry
