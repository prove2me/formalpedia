-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_ne_zero_of_nonzero_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:19.921359+00:00
-- url     : https://prove2.me/theorems/b71d3b68-0839-4f3f-be7f-2185df0f4d62
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift ne zero of nonzero code
-- statement:
--   The literal second-cut source code lift is nonzero whenever the code carrier is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L62-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L62-L89

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    M.secondCutCodeLift region ≠ 0 := by sorry
