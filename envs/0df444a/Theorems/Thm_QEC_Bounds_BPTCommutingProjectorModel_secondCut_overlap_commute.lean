-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_overlap_commute
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_overlap_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:17:02.6381+00:00
-- url     : https://prove2.me/theorems/678a4f6b-431b-4602-8195-41dca0de5119
-- title:
--   BPTCommuting Projector Model: second Cut overlap commute
-- statement:
--   The concrete `AB / B bar(M)` overlap pair commutes in second-cut coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L404-L447
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L404-L447

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_overlap_commute
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region))
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) := by sorry
