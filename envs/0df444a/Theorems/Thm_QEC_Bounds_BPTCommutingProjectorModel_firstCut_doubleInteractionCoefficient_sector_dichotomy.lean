-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_doubleInteractionCoefficient_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_doubleInteractionCoefficient_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:27:12.129192+00:00
-- url     : https://prove2.me/theorems/f9d32604-f94f-4f05-a7d6-e4043e032310
-- title:
--   BPTCommuting Projector Model: first Cut double Interaction Coefficient sector dichotomy
-- statement:
--   External-boundary correctability supplies the exact `hsector` premise for
--   every first-cut double coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4349-L4377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4349-L4377

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_doubleInteractionCoefficient_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) :
    M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0 ∨
      M.firstCutDoubleInteractionCoefficient region d d' a a' *
        leftIsotypicSectorProjector (M.firstCutProjectorMC region) component =
        M.firstCutDoubleInteractionCoefficient region d d' a a' := by sorry
