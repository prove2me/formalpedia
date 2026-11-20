-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyAssociator_symm_conj_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_tensorMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:54:06.191355+00:00
-- url     : https://prove2.me/theorems/4c36ff5b-f41d-4a1c-94c2-5ba4c541b345
-- title:
--   BPTCommuting Projector Model: final Assembly Associator symm conj tensor Map
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Associator symm conj tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorSpecialization.lean#L24-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/AssociatorSpecialization.lean#L24-L45

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_AssociatorSpecialization
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000

noncomputable def QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyAssociator_symm_conj_tensorMap
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
          (TensorProduct.map A0
            (TensorProduct.map (1 : Semantics.Operator X) (1 : Semantics.Operator D))) =
        TensorProduct.map (TensorProduct.map A0 (1 : Semantics.Operator X))
          (1 : Semantics.Operator D) := by sorry
