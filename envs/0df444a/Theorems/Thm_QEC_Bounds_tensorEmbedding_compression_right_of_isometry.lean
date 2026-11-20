-- Prove2me | Theorems.Thm_QEC_Bounds_tensorEmbedding_compression_right_of_isometry
-- name    : QEC.Bounds.tensorEmbedding_compression_right_of_isometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:31:52.060646+00:00
-- url     : https://prove2.me/theorems/226e9a2f-ed8c-4113-94b7-c78952209bb6
-- title:
--   Bounds: tensor Embedding compression right of isometry
-- statement:
--   Compress a right tensor action through an isometric left embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L93-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L93-L107

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v

theorem QEC.Bounds.tensorEmbedding_compression_right_of_isometry
    {H K H' K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup H'] [InnerProductSpace Complex H'] [Semantics.FiniteQuantumSystem H']
    [NormedAddCommGroup K'] [InnerProductSpace Complex K'] [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗᵢ[Complex] H') (eK : K →ₗ[Complex] K')
    (B : Semantics.Operator K') :
    (LinearMap.adjoint (TensorProduct.map eH.toLinearMap eK)).comp
        ((TensorProduct.map (1 : Semantics.Operator H') B).comp
          (TensorProduct.map eH.toLinearMap eK)) =
      TensorProduct.map (1 : Semantics.Operator H)
        ((LinearMap.adjoint eK).comp (B.comp eK)) := by sorry
