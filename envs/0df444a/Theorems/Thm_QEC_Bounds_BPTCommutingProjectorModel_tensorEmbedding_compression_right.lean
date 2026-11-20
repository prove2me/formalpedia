-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorEmbedding_compression_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorEmbedding_compression_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:13.407107+00:00
-- url     : https://prove2.me/theorems/96efc864-f9ca-478d-b5af-828327b4c936
-- title:
--   BPTCommuting Projector Model: tensor Embedding compression right
-- statement:
--   Compressing a right tensor action through two isometric embeddings leaves the left identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L125-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L125-L143

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorEmbedding_compression_right
    {H K H' K' : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup H'] [InnerProductSpace Complex H']
    [Semantics.FiniteQuantumSystem H'] [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗ[Complex] H') (eK : K →ₗ[Complex] K')
    (heH : (LinearMap.adjoint eH).comp eH = (1 : Semantics.Operator H))
    (B : Semantics.Operator K') :
    (LinearMap.adjoint (TensorProduct.map eH eK)).comp
        ((TensorProduct.map (1 : Semantics.Operator H') B).comp
          (TensorProduct.map eH eK)) =
      TensorProduct.map (1 : Semantics.Operator H)
        ((LinearMap.adjoint eK).comp (B.comp eK)) := by sorry
