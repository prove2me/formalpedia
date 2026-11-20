-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorEmbedding_compression_left
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorEmbedding_compression_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:10.911036+00:00
-- url     : https://prove2.me/theorems/c5647887-d5b6-4711-83dd-ab15f02ff15c
-- title:
--   BPTCommuting Projector Model: tensor Embedding compression left
-- statement:
--   Compressing a left tensor action through two isometric embeddings leaves the right identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L104-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L104-L122

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorEmbedding_compression_left
    {H K H' K' : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup H'] [InnerProductSpace Complex H']
    [Semantics.FiniteQuantumSystem H'] [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗ[Complex] H') (eK : K →ₗ[Complex] K')
    (heK : (LinearMap.adjoint eK).comp eK = (1 : Semantics.Operator K))
    (A : Semantics.Operator H') :
    (LinearMap.adjoint (TensorProduct.map eH eK)).comp
        ((TensorProduct.map A (1 : Semantics.Operator K')).comp
          (TensorProduct.map eH eK)) =
      TensorProduct.map ((LinearMap.adjoint eH).comp (A.comp eH))
        (1 : Semantics.Operator K) := by sorry
