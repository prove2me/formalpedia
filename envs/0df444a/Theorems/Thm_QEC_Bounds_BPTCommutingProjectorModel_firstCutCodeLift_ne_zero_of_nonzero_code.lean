-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_ne_zero_of_nonzero_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:36:59.131279+00:00
-- url     : https://prove2.me/theorems/7fc3e296-fb52-4202-bf11-e7c0a42ad5f4
-- title:
--   BPTCommuting Projector Model: first Cut Code Lift ne zero of nonzero code
-- statement:
--   The literal first-cut source code lift is nonzero whenever the code carrier is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeNonzero.lean#L24-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/FirstCutCodeNonzero.lean#L24-L50

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    M.firstCutCodeLift region ≠ 0 := by sorry
