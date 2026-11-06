-- Prove2me | Theorems.Thm_QEC_Bounds_complementEmbedding_intertwines_coordinates
-- name    : QEC.Bounds.complementEmbedding_intertwines_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:38:00.732202+00:00
-- url     : https://prove2.me/theorems/cc3d5737-3d5c-4cb4-a822-13abb431f213
-- title:
--   Bounds: complement Embedding intertwines coordinates
-- statement:
--   The Bounds construction uses the complement Embedding intertwines coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/ComplementIntertwiningCore.lean#L22-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/ComplementIntertwiningCore.lean#L22-L104

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_TensorCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ComplementIntertwiningCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 60000

theorem QEC.Bounds.complementEmbedding_intertwines_coordinates
    {W N C D H : Type u}
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (split : Semantics.UnitaryTransport H (Semantics.CompositeSystem C D))
    (eC : Semantics.CompositeSystem W N →ₗ[Complex] C)
    (Z : Semantics.Operator D) :
    let reassociate := BPTCommutingProjectorModel.tensorAssociatorUnitary W N D
    let J := TensorProduct.map eC (1 : Semantics.Operator D)
    let Ecd := J.comp reassociate.symm.toLinearEquiv.toLinearMap
    let P : Semantics.Operator (Semantics.CompositeSystem C D) :=
      TensorProduct.map (1 : Semantics.Operator C) Z
    let Pin : Semantics.Operator (Semantics.CompositeSystem W
        (Semantics.CompositeSystem N D)) :=
      TensorProduct.map (1 : Semantics.Operator W)
        (TensorProduct.map (1 : Semantics.Operator N) Z)
    (split.symm.conjOperator P).comp
        (split.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (split.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Pin := by sorry
