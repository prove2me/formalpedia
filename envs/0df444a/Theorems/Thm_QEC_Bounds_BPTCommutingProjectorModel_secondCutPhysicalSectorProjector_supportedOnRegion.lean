-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutPhysicalSectorProjector_supportedOnRegion
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_supportedOnRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:23.791801+00:00
-- url     : https://prove2.me/theorems/6c158e3e-5686-451c-a551-47599836ad99
-- title:
--   BPTCommuting Projector Model: second Cut Physical Sector Projector supported On Region
-- statement:
--   A physical second-cut sector is supported on the recovered region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L552-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L552-L566

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_supportedOnRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.regionSubsystem region).OperatorSupportedOnRegister
      (M.secondCutPhysicalSectorProjector region component) := by sorry
