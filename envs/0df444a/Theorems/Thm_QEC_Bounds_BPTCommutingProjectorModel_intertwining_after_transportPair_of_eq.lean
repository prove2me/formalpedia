-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_intertwining_after_transportPair_of_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.intertwining_after_transportPair_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:10.594769+00:00
-- url     : https://prove2.me/theorems/625f5129-870c-4901-ac79-2f0586c9bdcc
-- title:
--   BPTCommuting Projector Model: intertwining after transport Pair of eq
-- statement:
--   The BPTCommuting Projector Model construction uses the intertwining after transport Pair of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningTransportCore.lean#L19-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/IntertwiningTransportCore.lean#L19-L68

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTensor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_IntertwiningTransportCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
universe u
open QEC.Bounds.BPTCommutingProjectorModel

theorem QEC.Bounds.BPTCommutingProjectorModel.intertwining_after_transportPair_of_eq
    {S H T K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K)
    (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (outputEmbedding : S →ₗ[Complex] K)
    (A : Semantics.Operator H) (Q : Semantics.Operator T) (D : Semantics.Operator S)
    (houtput : outputEmbedding = outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding))
    (hcoordinates : coordinates.conjOperator A = Q)
    (hembedding : Q.comp embedding = embedding.comp D) :
    (outer.conjOperator A).comp outputEmbedding = outputEmbedding.comp D := by sorry
