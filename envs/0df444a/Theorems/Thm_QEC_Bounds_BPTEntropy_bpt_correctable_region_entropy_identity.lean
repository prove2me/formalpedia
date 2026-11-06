-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_correctable_region_entropy_identity
-- name    : QEC.Bounds.BPTEntropy.bpt_correctable_region_entropy_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:13.449134+00:00
-- url     : https://prove2.me/theorems/1bbbbe9f-acaa-4dfe-9161-d7326ae9e1b4
-- title:
--   BPTEntropy: bpt correctable region entropy identity
-- statement:
--   The source-faithful BPT-model specialization of
--   `erasure_correctable_entropy_identity`.  Its quantified density operator is
--   supported on the actual common-fixed commuting-projector code from #378.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L270-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L270-L282

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

theorem QEC.Bounds.BPTEntropy.bpt_correctable_region_entropy_identity
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ) (region : Finset L.Site)
    (recovery : QuantumChannel (M.regionSubsystem region).complementSystem L.Register)
    (hcorrect : Correctable L.Register (M.regionSubsystem region).complementSystem M.codeSpace
      (M.regionSubsystem region).erasureChannelFromRegister recovery)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    rho.vonNeumannEntropy -
        ((M.regionSubsystem region).erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by sorry
