-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_toOperator
-- name    : QEC.Bounds.BPTEntropy.normalizedCodeProjector_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:36.794097+00:00
-- url     : https://prove2.me/theorems/04867ff8-11bf-4a3f-b332-11c787f56727
-- title:
--   BPTEntropy: normalized Code Projector to Operator
-- statement:
--   `Lambda` is exactly the full-code projector divided by the code dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L536-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L536-L582

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.normalizedCodeProjector_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).toOperator =
      ((C.dimension : Real)⁻¹ : Complex) • C.projector := by sorry
