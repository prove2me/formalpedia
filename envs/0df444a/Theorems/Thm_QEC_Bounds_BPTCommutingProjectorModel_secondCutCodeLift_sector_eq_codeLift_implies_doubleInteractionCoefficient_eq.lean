-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:43.016417+00:00
-- url     : https://prove2.me/theorems/c471936b-8d98-413b-92f6-f0212003172f
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift sector eq code Lift implies double Interaction Coefficient eq
-- statement:
--   A full second-cut code sector fixes every corresponding coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L710-L727
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L710-L727

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hfull : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
      M.secondCutDoubleInteractionCoefficient region cd cd' a a' := by sorry
