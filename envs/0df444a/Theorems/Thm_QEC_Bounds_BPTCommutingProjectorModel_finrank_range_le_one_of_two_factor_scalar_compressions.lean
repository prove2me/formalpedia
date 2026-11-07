-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finrank_range_le_one_of_two_factor_scalar_compressions
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finrank_range_le_one_of_two_factor_scalar_compressions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:30:44.561144+00:00
-- url     : https://prove2.me/theorems/31662b0d-051a-4cc0-8233-5d98081b63ec
-- title:
--   BPTCommuting Projector Model: finrank range le one of two factor scalar compressions
-- statement:
--   Two independent local scalar-compression families on a genuine two-factor
--   projection force its range to have finite complex dimension at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L487-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L487-L532

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

theorem QEC.Bounds.BPTCommutingProjectorModel.finrank_range_le_one_of_two_factor_scalar_compressions
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    Module.finrank Complex (LinearMap.range P) ≤ 1 := by sorry
