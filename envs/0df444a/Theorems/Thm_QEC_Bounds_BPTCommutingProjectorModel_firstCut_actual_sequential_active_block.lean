-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_actual_sequential_active_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_actual_sequential_active_block
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T17:08:13.070033+00:00
-- url     : https://prove2.me/theorems/b386ab30-2eae-4fd4-a7c5-ac772307bda5
-- title:
--   BPTCommuting Projector Model: first Cut actual sequential active block
-- statement:
--   The concrete C-first sequential block for the BPT code.  The physical
--   first-cut BV03 product is compressed through the literal active `B` subtype
--   using the proved left-factor naturality square, then transported by the
--   actual `B` isotypic unitary.  This is the actual `hfirst` input to the common
--   factorization step, with `P_D` retained unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutActive.lean#L41-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutActive.lean#L41-L121

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_FirstCutBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveBlockTransports
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Factors
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActiveData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutActive
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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_actual_sequential_active_block
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
    (Pfirst : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (WC.restrictScalars Complex)))
    (P_D : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
        (M.fourFactorD region)))
    (hleft :
      (unitaryLTensor
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) UC).conjOperator
          (overlapProjectorOnIsotypicComponent (M.firstCutProjectorMC region) ccomponent) =
        rightTensorExtensionAfterLeft
          (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (WC.restrictScalars Complex) (isotypicLiftedMultiplicity.{0} nC) Pfirst)
    (hright :
      (unitaryRTensor UC (M.fourFactorD region)).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region) ccomponent) =
        leftTensorExtensionBeforeRight (WC.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{0} nC) (M.fourFactorD region) P_D) :
    FirstCutActualSequentialActiveBlock M region bcomponent ccomponent WB WC UB UC Pfirst P_D := by sorry
