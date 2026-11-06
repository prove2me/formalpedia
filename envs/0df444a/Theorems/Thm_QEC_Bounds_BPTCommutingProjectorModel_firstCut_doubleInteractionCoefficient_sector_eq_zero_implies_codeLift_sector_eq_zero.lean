-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:27:26.781524+00:00
-- url     : https://prove2.me/theorems/ef68587d-7688-446e-96c5-ad1dc03979ae
-- title:
--   BPTCommuting Projector Model: first Cut double Interaction Coefficient sector eq zero implies code Lift sector eq zero
-- statement:
--   For a nonzero double coefficient, an inactive coefficient sector cannot arise
--   from a full code sector.  Thus the physical first-cut sector is zero as well.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4422-L4441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4422-L4441

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hnonzero : M.firstCutDoubleInteractionCoefficient region d d' a a' ≠ 0)
    (hzero : M.firstCutDoubleInteractionCoefficient region d d' a a' *
      leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0) :
    M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 := by sorry
