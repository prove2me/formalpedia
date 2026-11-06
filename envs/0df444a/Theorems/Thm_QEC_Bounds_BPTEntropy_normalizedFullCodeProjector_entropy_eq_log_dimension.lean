-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_entropy_eq_log_dimension
-- name    : QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_log_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:35:28.118051+00:00
-- url     : https://prove2.me/theorems/8dc62250-3574-404b-b8f0-e8db408f260a
-- title:
--   BPTEntropy: normalized Full Code Projector entropy eq log dimension
-- statement:
--   The normalized full-code-projector state has entropy `log2 (dim C)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L866-L874
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L866-L874

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

theorem QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_log_dimension
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      Real.logb 2 (M.codeSpace.dimension : Real) := by sorry
