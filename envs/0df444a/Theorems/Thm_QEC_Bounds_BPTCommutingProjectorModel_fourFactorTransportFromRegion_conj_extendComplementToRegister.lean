-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_conj_extendComplementToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_conj_extendComplementToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:26.539796+00:00
-- url     : https://prove2.me/theorems/735a9143-cc8d-473b-b293-c279f6ab7ad2
-- title:
--   BPTCommuting Projector Model: four Factor Transport From Region conj extend Complement To Register
-- statement:
--   Under the `AB`-first four-factor transport, a complement-local operator is
--   the identity on `A B` tensored with its explicitly split `C D` action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1806-L1857
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1806-L1857

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransportFromRegion_conj_extendComplementToRegister
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    (M.fourFactorTransportFromRegion region).conjOperator
        (extendComplementToRegister (M.regionSubsystem region) P) =
      M.fourFactorExtendCD region
        (((M.regionSubsystem region).complementFactorization
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            exact Finset.mem_union_left _ hsite)).conjOperator P) := by sorry
