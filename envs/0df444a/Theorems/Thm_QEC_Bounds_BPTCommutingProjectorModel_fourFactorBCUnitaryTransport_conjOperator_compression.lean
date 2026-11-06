-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_conjOperator_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_conjOperator_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:31.345238+00:00
-- url     : https://prove2.me/theorems/a45f3630-849f-452a-849b-7534c3c86712
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport conj Operator compression
-- statement:
--   The preceding two intertwining lemmas give the exact D3/D4 compressed-block
--   transport in canonical four-factor coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L467-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sector.lean#L467-L493

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_conjOperator_compression
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
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))) :
    (LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
        (((fourFactorBCUnitaryTransport (A := A) (D := D) E).conjOperator P).comp
          (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)) =
      (jointBCSectorActiveUnitary (A := A) pB pC V).conjOperator
        ((LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
          (P.comp (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC))) := by sorry
