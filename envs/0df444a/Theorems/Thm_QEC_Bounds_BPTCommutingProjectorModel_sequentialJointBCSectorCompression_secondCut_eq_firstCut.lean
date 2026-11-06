-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequentialJointBCSectorCompression_secondCut_eq_firstCut
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequentialJointBCSectorCompression_secondCut_eq_firstCut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T17:08:00.052453+00:00
-- url     : https://prove2.me/theorems/13b2074b-4a65-4952-b412-bfa2aef293b0
-- title:
--   BPTCommuting Projector Model: sequential Joint BCSector Compression second Cut eq first Cut
-- statement:
--   The common joint B/C block written as the two sequential compressions which
--   the first- and second-cut BV03 block equations act on.  This is a direct
--   expansion of `jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Compression.lean#L28-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Compression.lean#L28-L60

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Compression
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.sequentialJointBCSectorCompression_secondCut_eq_firstCut
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let V := tensorAssociatorUnitary
      (Semantics.CompositeSystem (M.fourFactorA region) pB) pC (M.fourFactorD region)
    M.sequentialSecondCutJointCompression region pB pC =
      V.conjOperator (M.sequentialFirstCutJointCompression region pB pC) := by sorry
