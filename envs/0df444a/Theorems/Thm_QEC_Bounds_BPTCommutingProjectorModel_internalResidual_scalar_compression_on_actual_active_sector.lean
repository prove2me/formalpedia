-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_internalResidual_scalar_compression_on_actual_active_sector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.internalResidual_scalar_compression_on_actual_active_sector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T06:04:43.046284+00:00
-- url     : https://prove2.me/theorems/23759d20-e884-40a8-9821-76250bea88e0
-- title:
--   BPTCommuting Projector Model: internal Residual scalar compression on actual active sector
-- statement:
--   Transport one fixed internal-residual probe through the active `C` sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/InternalTransport.lean#L27-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/InternalTransport.lean#L27-L191

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_InternalTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000

theorem QEC.Bounds.BPTCommutingProjectorModel.internalResidual_scalar_compression_on_actual_active_sector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (X : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB)) (scalar : Complex)
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hscalar : M.PhysicalInternalResidualProbeCompression
      region Qsecond X scalar) :
    M.ActualInternalResidualProbeCompression
      region ccomponent WC UC Qsecond X scalar := by sorry
