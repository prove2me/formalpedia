-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_encodedQubits_le_complement_log_dimensions
-- name    : QEC.Bounds.BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:36:49.989705+00:00
-- url     : https://prove2.me/theorems/a1d95505-4973-4f32-8e0f-38985c1fa2e8
-- title:
--   BPTEntropy: bpt encoded Qubits le complement log dimensions
-- statement:
--   The #378 power-of-two convention turns the normalized-state BPT entropy
--   bound into the encoded-qubit inequality `k <= log dim(C)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1512-L1534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1512-L1534

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

theorem QEC.Bounds.BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (A B : Finset L.Site) (hdisjoint : Disjoint A B)
    (recoveryA : QuantumChannel (M.regionSubsystem A).complementSystem L.Register)
    (hcorrectA : Correctable L.Register (M.regionSubsystem A).complementSystem M.codeSpace
      (M.regionSubsystem A).erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel (M.regionSubsystem B).complementSystem L.Register)
    (hcorrectB : Correctable L.Register (M.regionSubsystem B).complementSystem M.codeSpace
      (M.regionSubsystem B).erasureChannelFromRegister recoveryB) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by sorry
