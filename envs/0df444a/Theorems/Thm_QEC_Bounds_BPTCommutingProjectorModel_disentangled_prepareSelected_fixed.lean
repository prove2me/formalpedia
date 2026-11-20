-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disentangled_prepareSelected_fixed
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disentangled_prepareSelected_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:08.351693+00:00
-- url     : https://prove2.me/theorems/440eb703-3ee8-435f-a843-6c4eef20ec24
-- title:
--   BPTCommuting Projector Model: disentangled prepare Selected fixed
-- statement:
--   The BPTCommuting Projector Model construction uses the disentangled prepare Selected fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L318-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/BlockRecursion.lean#L318-L380

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem QEC.Bounds.BPTCommutingProjectorModel.disentangled_prepareSelected_fixed
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (unitary : UnitaryTransport L.Register L.Register)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Operator (M.regionSubsystem region).complementSystem)
    (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
    (regionalState_normalized : ‖regionalState‖ = 1)
    (projector_factorization :
      unitary.conjOperator M.fullCodeProjector =
        M.pureFactorTensorComplementProjector region regionalState complementProjector)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    (M.regionSubsystem region).prepareSelected
      (pureDensity regionalState (by rw [regionalState_normalized]; norm_num))
      ((M.regionSubsystem region).erasureChannelFromRegister
        (unitary.conjOperator rho.toOperator)) =
      unitary.conjOperator rho.toOperator := by sorry
