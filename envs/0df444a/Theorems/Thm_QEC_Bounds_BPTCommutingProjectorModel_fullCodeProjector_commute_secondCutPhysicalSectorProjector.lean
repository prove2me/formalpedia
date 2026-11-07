-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_commute_secondCutPhysicalSectorProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_commute_secondCutPhysicalSectorProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:16.303196+00:00
-- url     : https://prove2.me/theorems/b2763ddd-00a5-41d4-bb31-32b039ec3241
-- title:
--   BPTCommuting Projector Model: full Code Projector commute second Cut Physical Sector Projector
-- statement:
--   The full code projector commutes with every physical second-cut sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L502-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L502-L549

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_commute_secondCutPhysicalSectorProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    Commute M.fullCodeProjector
      (M.secondCutPhysicalSectorProjector region component) := by sorry
