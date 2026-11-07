-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regroup_actual_active_sector_scalar_compressions
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T07:35:33.90654+00:00
-- url     : https://prove2.me/theorems/c2ad3e32-6bb2-4c05-842f-feb26b71b19f
-- title:
--   BPTCommuting Projector Model: regroup actual active sector scalar compressions
-- statement:
--   Reassociate both exact active-sector scalar-compression families.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Regrouping.lean#L50-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Regrouping.lean#L50-L113

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions
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
    (hrawInternal :
      M.ActualInternalResidualScalarCompression region ccomponent WC UC Qsecond)
    (hrawExternal :
      M.ActualExternalResidualScalarCompression region ccomponent WC UC Qsecond) :
    RegroupedTwoFactorScalarCompressions
      (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond) := by sorry
