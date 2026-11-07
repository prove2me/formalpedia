-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:42.03521+00:00
-- url     : https://prove2.me/theorems/6a152c4c-25cc-4f7a-aa58-4add075c6771
-- title:
--   BPTCommuting Projector Model: second Cut double Interaction Coefficient sector eq zero implies code Lift sector eq zero
-- statement:
--   For a nonzero second-cut double coefficient, an inactive coefficient sector
--   cannot arise from a full code sector, so the physical code sector is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L733-L752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L733-L752

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hnonzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' ≠ 0)
    (hzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
      leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0) :
    M.secondCutCodeLift region * M.secondCutSectorLift region component = 0 := by sorry
