-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_actual_sequential_active_block_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_actual_sequential_active_block_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T17:04:17.350769+00:00
-- url     : https://prove2.me/theorems/76e3d8cb-941f-484d-87be-c2f70e0292ee
-- title:
--   BPTCommuting Projector Model: second Cut actual sequential active block of region recoverable
-- statement:
--   The concrete B-first sequential block for the BPT code.  The source
--   rank-one `Pi_AB'` equation is obtained from `hM`, then its literal active
--   `C` subtype compression is transported by the proved right-factor
--   naturality square.  This supplies the actual `hsecond` input to the common
--   factorization step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutActive.lean#L39-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutActive.lean#L39-L101

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutActive
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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_actual_sequential_active_block_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) (hM : M.RegionErasureRecoverable region)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hsource : SecondCutActiveBlockConditions M region bcomponent WB UB Pleft Qsecond) :
    SecondCutActualSequentialActiveBlock M region bcomponent ccomponent WB WC UB UC Qsecond := by sorry
