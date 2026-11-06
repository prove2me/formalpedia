-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:27:58.051881+00:00
-- url     : https://prove2.me/theorems/d28d4be2-b24b-4213-9932-9fd10ceee7c8
-- title:
--   BPTCommuting Projector Model: joint BCSector Compression second Cut Code Lift eq first Cut Code Lift
-- statement:
--   The common first/second-cut block equality for the actual BPT code lift.
--   Both sides are literal simultaneous `B,C` sector compressions of the same
--   full code projector, expressed in their respective block parenthesizations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L155-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L155-L185

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_secondCutCodeLift_eq_firstCutCodeLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    let A := M.fourFactorA region
    let D := M.fourFactorD region
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft (A := A) pB pC
    let Jright := jointBCSectorEmbeddingRight (A := A) pB pC
    (LinearMap.adjoint Jright).comp ((M.secondCutCodeLift region).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp ((M.firstCutCodeLift region).comp Jleft)) := by sorry
