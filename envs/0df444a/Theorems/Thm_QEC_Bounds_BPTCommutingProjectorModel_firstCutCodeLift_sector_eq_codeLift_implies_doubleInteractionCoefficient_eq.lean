-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:32.455724+00:00
-- url     : https://prove2.me/theorems/f0ad7c3b-1ceb-4eb6-a636-53c53c653e60
-- title:
--   BPTCommuting Projector Model: first Cut Code Lift sector eq code Lift implies double Interaction Coefficient eq
-- statement:
--   A full first-cut code sector fixes every corresponding double coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4399-L4416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4399-L4416

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hfull : M.firstCutCodeLift region * M.firstCutSectorLift region component =
      M.firstCutCodeLift region) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
      M.firstCutDoubleInteractionCoefficient region d d' a a' := by sorry
