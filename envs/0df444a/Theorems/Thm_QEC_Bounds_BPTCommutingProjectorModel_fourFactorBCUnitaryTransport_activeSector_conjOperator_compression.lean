-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_activeSector_conjOperator_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_activeSector_conjOperator_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:43.721225+00:00
-- url     : https://prove2.me/theorems/6107134f-0040-40a2-ad9c-f248dc8d6c9d
-- title:
--   BPTCommuting Projector Model: four Factor BCUnitary Transport active Sector conj Operator compression
-- statement:
--   The D3 physical lift transports the D4 joint compression by the corresponding
--   active-sector coordinate unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L104-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L104-L132

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_activeSector_conjOperator_compression
    {A B C D WB NB WC NC : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))) :
    (LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
        (((fourFactorBCUnitaryTransport (A := A) (D := D)
          (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator P).comp
          (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)) =
      (jointBCSectorActiveUnitary (A := A) pB pC
        (activeSectorJointBCUnitary pB pC UB UC U)).conjOperator
        ((LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
          (P.comp (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC))) := by sorry
