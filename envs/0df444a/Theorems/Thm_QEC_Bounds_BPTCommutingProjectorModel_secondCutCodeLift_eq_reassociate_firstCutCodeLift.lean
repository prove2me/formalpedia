-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_eq_reassociate_firstCutCodeLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_eq_reassociate_firstCutCodeLift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:26:13.713955+00:00
-- url     : https://prove2.me/theorems/c96c47c4-4960-4054-999d-d5e7648209eb
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift eq reassociate first Cut Code Lift
-- statement:
--   The two literal BPT cut lifts are the same physical code operator, related by
--   the explicit associator from `((AB)C)D` to `(AB)(CD)`.  This is the concrete
--   first/second-cut equality from which the joint-sector `Theta tensor Pi_C''D`
--   block must be reconstructed; no tensor factorization is assumed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L29-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L29-L60

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_eq_reassociate_firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
      (M.fourFactorC region) (M.fourFactorD region)).conjOperator
        (M.firstCutCodeLift region) = M.secondCutCodeLift region := by sorry
