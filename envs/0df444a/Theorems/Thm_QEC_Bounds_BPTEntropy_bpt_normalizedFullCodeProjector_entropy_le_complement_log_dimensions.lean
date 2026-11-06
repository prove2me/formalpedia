-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions
-- name    : QEC.Bounds.BPTEntropy.bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:28:18.057297+00:00
-- url     : https://prove2.me/theorems/22ce58a3-c907-41d6-b2b5-499fe616f595
-- title:
--   BPTEntropy: bpt normalized Full Code Projector entropy le complement log dimensions
-- statement:
--   The source-faithful BPT entropy inequality for the normalized full-code
--   projector.  `A` and `B` are concrete disjoint lattice regions with actual
--   recovery maps for their `erasureChannelFromRegister` channels.  Their two
--   correctability identities are transported into the explicit `A tensor (B
--   tensor C)` calculation, whose two subadditivity steps bound `S(Lambda)` by the
--   heterogeneous local-dimension logarithm sum on `C`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1450-L1508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L1450-L1508

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

theorem QEC.Bounds.BPTEntropy.bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions
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
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by sorry
