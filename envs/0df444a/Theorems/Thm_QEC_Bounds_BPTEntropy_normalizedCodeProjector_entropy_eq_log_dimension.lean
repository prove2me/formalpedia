-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_entropy_eq_log_dimension
-- name    : QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_log_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:49:00.579871+00:00
-- url     : https://prove2.me/theorems/faa5f4b5-efa0-4f7c-a9f7-edf2600eaab9
-- title:
--   BPTEntropy: normalized Code Projector entropy eq log dimension
-- statement:
--   The normalized full-code projector has entropy `log2 (dim C)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L791-L808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L791-L808

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

theorem QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_log_dimension {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).vonNeumannEntropy =
      Real.logb 2 (C.dimension : Real) := by sorry
