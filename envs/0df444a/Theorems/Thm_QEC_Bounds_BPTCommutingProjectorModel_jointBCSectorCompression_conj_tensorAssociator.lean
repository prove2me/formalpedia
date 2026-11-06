-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorCompression_conj_tensorAssociator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_conj_tensorAssociator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:27:58.83954+00:00
-- url     : https://prove2.me/theorems/db7ceb84-57a2-4f5b-9baf-8b1a19469c7f
-- title:
--   BPTCommuting Projector Model: joint BCSector Compression conj tensor Associator
-- statement:
--   Compressing a real four-factor operator to both active boundary sectors
--   commutes with the physical first/second-cut reassociation.  This is an
--   operator equality, not a support statement: it is the common block on which
--   the two source tensor factorizations are compared.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L77-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Compression/Transport.lean#L77-L147

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

theorem QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_conj_tensorAssociator
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (T : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) D)) :
    let U := tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft pB pC
    let Jright := jointBCSectorEmbeddingRight pB pC
    (LinearMap.adjoint Jright).comp ((U.conjOperator T).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp (T.comp Jleft)) := by sorry
