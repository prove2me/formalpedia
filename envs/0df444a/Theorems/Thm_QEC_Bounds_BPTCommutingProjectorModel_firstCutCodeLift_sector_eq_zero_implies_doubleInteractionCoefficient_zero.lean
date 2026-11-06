-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:08.722781+00:00
-- url     : https://prove2.me/theorems/e2167da7-5b49-4b0c-b791-a358bbe9d9c1
-- title:
--   BPTCommuting Projector Model: first Cut Code Lift sector eq zero implies double Interaction Coefficient zero
-- statement:
--   A zero first-cut code sector forces every corresponding double coefficient to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4380-L4396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4380-L4396

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_eq_zero_implies_doubleInteractionCoefficient_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hzero : M.firstCutCodeLift region * M.firstCutSectorLift region component = 0) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 := by sorry
