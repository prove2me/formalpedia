-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:29:56.605173+00:00
-- url     : https://prove2.me/theorems/e8d3a674-7925-4139-9a07-a8b54ebef986
-- title:
--   BPTCommuting Projector Model: partial Trace Right Raw rank One eq inner smul of left scalar compression
-- statement:
--   One-factor scalar compression fixes every code cross term after tracing out
--   the opposite factor.  This is the local reference-decoupling bridge used by
--   the two-factor no-cloning closure; it only consumes probes on `N`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L28-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L28-L118

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

theorem QEC.Bounds.BPTCommutingProjectorModel.partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y) (hnorm : inner Complex x x = 1) :
    Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • Semantics.partialTraceRightRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap := by sorry
