-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:32.427201+00:00
-- url     : https://prove2.me/theorems/0c5699e3-9e7c-4493-80f9-d9a47e1f3d37
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift sector eq zero implies double Interaction Coefficient zero
-- statement:
--   A zero second-cut code sector forces every corresponding coefficient to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L691-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L691-L707

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hzero : M.secondCutCodeLift region * M.secondCutSectorLift region component = 0) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 := by sorry
