-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_expandedExteriorLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_expandedExteriorLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:17.111867+00:00
-- url     : https://prove2.me/theorems/bd93e0fd-9c7c-42d5-b288-130b9657e862
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj expanded Exterior Lift
-- statement:
--   The BPTCommuting Projector Model construction uses the four Factor Transport conj expanded Exterior Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L17-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L17-L113

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_expandedExteriorLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorD region)) :
    (M.fourFactorTransport region).conjOperator
      (extendComplementToRegister
        (M.regionSubsystem (region ∪ M.externalBoundary region)) Z) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by sorry
