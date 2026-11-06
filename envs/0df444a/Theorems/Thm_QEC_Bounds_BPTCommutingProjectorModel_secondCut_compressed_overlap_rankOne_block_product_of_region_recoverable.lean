-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:51:43.249758+00:00
-- url     : https://prove2.me/theorems/c3b2ac42-f9e5-4ac5-bf71-66fae17e9fba
-- title:
--   BPTCommuting Projector Model: second Cut compressed overlap rank One block product of region recoverable
-- statement:
--   The BPTCommuting Projector Model construction uses the second Cut compressed overlap rank One block product of region recoverable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneBlock.lean#L89-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftRankOneBlock.lean#L89-L121

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_compressed_overlap_rankOne_block_product_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (W.restrictScalars Complex)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hsource : SecondCutActiveBlockConditions M region component W U Pleft Qright) :
    SecondCutRankOneBlockProduct M region component W U Qright := by sorry
