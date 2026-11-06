-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_entropy_eq_encodedQubits
-- name    : QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_encodedQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:08.324105+00:00
-- url     : https://prove2.me/theorems/1d15ef59-a464-461e-ad3c-d5853cb93283
-- title:
--   BPTEntropy: normalized Full Code Projector entropy eq encoded Qubits
-- statement:
--   The #378 power-of-two convention turns `S(Lambda) = log2 (dim C)` into
--   the BPT encoded-qubit identity `S(Lambda) = k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L878-L885
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L878-L885

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

theorem QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_encodedQubits
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by sorry
