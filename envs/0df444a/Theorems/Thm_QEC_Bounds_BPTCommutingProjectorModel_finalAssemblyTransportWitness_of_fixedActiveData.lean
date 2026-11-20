-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyTransportWitness_of_fixedActiveData
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyTransportWitness_of_fixedActiveData
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:13:22.419055+00:00
-- url     : https://prove2.me/theorems/985c202c-3f7f-4289-9e42-720da718f48d
-- title:
--   BPTCommuting Projector Model: final Assembly Transport Witness of fixed Active Data
-- statement:
--   The BPTCommuting Projector Model construction uses the final Assembly Transport Witness of fixed Active Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransport.lean#L29-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransport.lean#L29-L263

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyTransportWitness_of_fixedActiveData
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
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
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (hfixed : M.FixedActiveDataProductRankOneTensor
      region bcomponent ccomponent WB WC UB UC P_D Qsecond) :
    FinalAssemblyTransportWitness M region bcomponent ccomponent WB WC UB UC P_D := by sorry
