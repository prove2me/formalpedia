-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_supportedOn
-- name    : QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:47.935873+00:00
-- url     : https://prove2.me/theorems/95e88a02-83a0-416a-b8bd-5a27e74bd6c8
-- title:
--   BPTEntropy: normalized Full Code Projector supported On
-- statement:
--   The BPT normalized full-code state is code-supported, so the universal
--   correctability identity applies to it without a pure-state restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L857-L863
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L857-L863

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

theorem QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_supportedOn
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    DensityOperator.SupportedOn M.codeSpace (normalizedFullCodeProjector M parameter) := by sorry
