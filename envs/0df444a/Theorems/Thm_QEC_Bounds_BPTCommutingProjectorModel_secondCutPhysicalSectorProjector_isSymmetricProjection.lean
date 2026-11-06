-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutPhysicalSectorProjector_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_isSymmetricProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:20.700078+00:00
-- url     : https://prove2.me/theorems/2e77561a-8869-4639-baa8-f7a790f1e16c
-- title:
--   BPTCommuting Projector Model: second Cut Physical Sector Projector is Symmetric Projection
-- statement:
--   A physical second-cut sector is an orthogonal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L461-L499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L461-L499

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.secondCutPhysicalSectorProjector region component).IsSymmetricProjection := by sorry
