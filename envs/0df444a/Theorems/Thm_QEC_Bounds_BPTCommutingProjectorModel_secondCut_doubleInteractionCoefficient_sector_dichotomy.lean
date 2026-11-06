-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_doubleInteractionCoefficient_sector_dichotomy
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_doubleInteractionCoefficient_sector_dichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:40.830203+00:00
-- url     : https://prove2.me/theorems/c5def22e-941a-4c4d-812f-39b774dfb701
-- title:
--   BPTCommuting Projector Model: second Cut double Interaction Coefficient sector dichotomy
-- statement:
--   Region correctability supplies the exact second-cut coefficient-sector
--   dichotomy required by finite isotypic-sector collapse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L660-L688
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L660-L688

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_doubleInteractionCoefficient_sector_dichotomy
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region) :
    M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0 ∨
      M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
        leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component =
        M.secondCutDoubleInteractionCoefficient region cd cd' a a' := by sorry
