-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressedCode_isSymmetricProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressedCode_isSymmetricProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:34:37.03895+00:00
-- url     : https://prove2.me/theorems/6c891544-c8aa-44b2-b4d7-e29aac7dcf8b
-- title:
--   BPTCommuting Projector Model: second Cut compressed Code is Symmetric Projection
-- statement:
--   The active second-cut code compressed to its selected isotypic sector is an
--   orthogonal projection.  This follows from the actual full code projector and
--   the proved sector commutation, and is used to obtain idempotence of `Qright`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L121-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L121-L145

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressedCode_isSymmetricProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    ((LinearMap.adjoint J).comp ((M.secondCutCodeLift region).comp J)).IsSymmetricProjection := by sorry
