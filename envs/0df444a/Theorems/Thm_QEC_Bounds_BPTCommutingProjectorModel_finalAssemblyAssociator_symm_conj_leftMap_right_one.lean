-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyAssociator_symm_conj_leftMap_right_one
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_leftMap_right_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:57:24.290189+00:00
-- url     : https://prove2.me/theorems/6c00981d-10c7-4739-bb83-73c35da2c388
-- title:
--   BPTCommuting Projector Model: final Assembly Associator symm conj left Map right one
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Associator symm conj left Map right one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorRightOne.lean#L24-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorRightOne.lean#L24-L56

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorRightOne
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_leftMap_right_one
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region)) :
    let H := Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
      (isotypicLiftedMultiplicity.{0} nB)
    let X := WC.restrictScalars Complex
    let D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
      (M.fourFactorD region)
    ∀ (A0 : Semantics.Operator H),
      (tensorAssociatorUnitary H X D).symm.conjOperator
          (TensorProduct.map A0 (1 : Semantics.Operator (Semantics.CompositeSystem X D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D) := by sorry
