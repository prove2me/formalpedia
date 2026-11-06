-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_commute_sectorCompressionProjection
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_commute_sectorCompressionProjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:35:23.719509+00:00
-- url     : https://prove2.me/theorems/7b9a9b4e-17c5-4943-8947-eb2f1846ab1c
-- title:
--   BPTCommuting Projector Model: second Cut Code Lift commute sector Compression Projection
-- statement:
--   The second-cut code lift commutes with compression to any selected sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L77-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ProjectionBlock.lean#L77-L114

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_commute_sectorCompressionProjection
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    let J := tensorTripleSubtypeEmbedding (A := A) (C := CD) H
    Commute (M.secondCutCodeLift region) (J.comp (LinearMap.adjoint J)) := by sorry
