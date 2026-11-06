-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:18.643214+00:00
-- url     : https://prove2.me/theorems/318b2c42-1f89-44bf-a485-18c5338336d0
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport intertwines joint BCSector Embedding
-- statement:
--   The four-factor lift of a physical `B,C` unitary intertwines the joint active
--   embedding with its prescribed active-sector coordinate action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L359-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L359-L417

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
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
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap.comp
        (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC) =
      (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC).comp
        (jointBCSectorActiveUnitary (A := A) pB pC V).toLinearEquiv.toLinearMap := by sorry
