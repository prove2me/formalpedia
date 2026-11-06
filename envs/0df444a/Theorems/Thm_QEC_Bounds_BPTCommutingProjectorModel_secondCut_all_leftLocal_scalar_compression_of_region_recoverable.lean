-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_all_leftLocal_scalar_compression_of_region_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_leftLocal_scalar_compression_of_region_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:29:26.039174+00:00
-- url     : https://prove2.me/theorems/a8265db3-5ad8-4eb2-90ec-028f88dff58f
-- title:
--   BPTCommuting Projector Model: second Cut all left Local scalar compression of region recoverable
-- statement:
--   Region correctability makes every literal `A tensor B` probe scalar on the
--   actual second-cut code lift.  The equality is transported from the physical
--   region-local extension, so this is the hM input for the source `Pi_AB'`
--   rank-one argument rather than an abstract code assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftPhysical.lean#L84-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftPhysical.lean#L84-L145

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_leftLocal_scalar_compression_of_region_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (E : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          overlapLiftLeft
            (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) E *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by sorry
