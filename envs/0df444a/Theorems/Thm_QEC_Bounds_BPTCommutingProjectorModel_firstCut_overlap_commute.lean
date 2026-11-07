-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_overlap_commute
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_overlap_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:15:51.439895+00:00
-- url     : https://prove2.me/theorems/6ad89226-dda0-46c7-bcc2-b1671626ff85
-- title:
--   BPTCommuting Projector Model: first Cut overlap commute
-- statement:
--   The concrete first-cut overlap pair commutes, inherited from the source products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2991-L3053
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2991-L3053

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_overlap_commute
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) := by sorry
