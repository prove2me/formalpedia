-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_entropy_eq_encodedQubits
-- name    : QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_encodedQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:51.277516+00:00
-- url     : https://prove2.me/theorems/0871ab49-d436-4c8b-a749-cefd86a325a9
-- title:
--   BPTEntropy: normalized Code Projector entropy eq encoded Qubits
-- statement:
--   The #378 power-of-two code-dimension witness realizes the BPT convention
--   `S(Lambda) = log2(dim C) = k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L812-L824
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L812-L824

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

theorem QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_encodedQubits
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedCodeProjector M.codeSpace (by
      rw [parameter.codeDimension_eq_two_pow]
      exact pow_pos (by omega) _)).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by sorry
