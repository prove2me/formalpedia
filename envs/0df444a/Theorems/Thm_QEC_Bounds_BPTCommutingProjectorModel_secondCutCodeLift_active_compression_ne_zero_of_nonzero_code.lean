-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:16.908673+00:00
-- url     : https://prove2.me/theorems/5c4ffaed-fcd7-4b06-8666-b4daae6fd1a8
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift active compression ne zero of nonzero code
-- statement:
--   A nonzero active second-cut sector has nonzero literal code compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L109-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L109-L130

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_active_compression_ne_zero_of_nonzero_code
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (hactive : M.secondCutCodeLift region * M.secondCutSectorLift region component =
      M.secondCutCodeLift region) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    ((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)) ≠ 0 := by sorry
