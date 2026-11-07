-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:29:38.228432+00:00
-- url     : https://prove2.me/theorems/14c6686e-302e-44ab-b6b8-3e077d9dadab
-- title:
--   BPTCommuting Projector Model: partial Trace Left Raw rank One self eq of right scalar compression
-- statement:
--   Right-factor scalar compression identifies the diagonal left marginals of any
--   two normalized vectors fixed by the projection.  This remains a one-factor
--   statement; no joint-observable scalarity is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L221-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L221-L293

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

theorem QEC.Bounds.BPTCommutingProjectorModel.partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y)
    (hnormx : inner Complex x x = 1) (hnormy : inner Complex y y = 1) :
    Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x x).toLinearMap =
      Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex y y).toLinearMap := by sorry
