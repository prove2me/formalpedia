-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_toOperator
-- name    : QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:34:44.00824+00:00
-- url     : https://prove2.me/theorems/aa498018-ebbb-4bb3-83ef-2e948aedeeca
-- title:
--   BPTEntropy: normalized Full Code Projector to Operator
-- statement:
--   The BPT normalized state is the full-code projector divided by `dim C`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L844-L853
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L844-L853

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

theorem QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_toOperator
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).toOperator =
      ((M.codeSpace.dimension : Real)⁻¹ : Complex) • M.fullCodeProjector := by sorry
