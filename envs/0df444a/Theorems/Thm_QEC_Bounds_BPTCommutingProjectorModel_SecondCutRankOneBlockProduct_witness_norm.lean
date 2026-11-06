-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_SecondCutRankOneBlockProduct_witness_norm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.SecondCutRankOneBlockProduct.witness_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:57:14.264693+00:00
-- url     : https://prove2.me/theorems/2d68f819-c733-4e6a-9fa6-17aa482c3976
-- title:
--   Second Cut Rank One Block Product: witness norm
-- statement:
--   The selected second-cut rank-one product witness is normalized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneProductWitnessNorm.lean#L20-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneProductWitnessNorm.lean#L20-L36

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.SecondCutRankOneBlockProduct.witness_norm
    {M : BPTCommutingProjectorModel L kappa} {region : Finset L.Site}
    {component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {n : Nat} [NeZero n]
    {W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n))}
    {Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))}
    (h : SecondCutRankOneBlockProduct (n := n) M region component W U Qright) :
    ‖SecondCutRankOneBlockProduct.witness (n := n) h‖ = 1 := by sorry
