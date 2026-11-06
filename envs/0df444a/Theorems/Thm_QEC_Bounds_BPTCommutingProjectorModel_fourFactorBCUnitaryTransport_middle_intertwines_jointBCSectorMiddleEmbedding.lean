-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:29.397987+00:00
-- url     : https://prove2.me/theorems/78ebd2ee-f505-4e9e-940b-3d306816bb3c
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport middle intertwines joint BCSector Middle Embedding
-- statement:
--   Tensoring an intertwining of the physical `B,C` sector embedding with the
--   outer spectators gives the corresponding middle-coordinate intertwining.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L307-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L307-L353

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap) :
    (unitaryLTensor A (unitaryRTensor E D)).toLinearEquiv.toLinearMap.comp
        (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC) =
      (jointBCSectorMiddleEmbedding (A := A) (D := D) pB pC).comp
        (unitaryLTensor A (unitaryRTensor V D)).toLinearEquiv.toLinearMap := by sorry
