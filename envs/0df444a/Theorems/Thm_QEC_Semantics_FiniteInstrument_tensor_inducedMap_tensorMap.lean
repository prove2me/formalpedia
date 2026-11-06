-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_inducedMap_tensorMap
-- name    : QEC.Semantics.FiniteInstrument.tensor_inducedMap_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:49.096479+00:00
-- url     : https://prove2.me/theorems/254aef52-8316-4ed7-8621-26221abe8723
-- title:
--   Finite Instrument: tensor induced Map tensor Map
-- statement:
--   The induced map of a tensor instrument acts factorwise on a literal
--   tensor-product operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L148-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L148-L177

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.tensor_inducedMap_tensorMap
    {kappa : Type v} {omega : Type w}
    {kappaTwo : Type x} {omegaTwo : Type y}
    [Fintype kappa] [Fintype kappaTwo] [Fintype omega] [Fintype omegaTwo]
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [FiniteQuantumSystem D]
    (first : FiniteInstrument kappa omega A B)
    (second : FiniteInstrument kappaTwo omegaTwo C D)
    (left : Operator A) (right : Operator C) :
    (first.tensor second).kraus.inducedMap
        (TensorProduct.map left right) =
      TensorProduct.map (first.kraus.inducedMap left)
        (second.kraus.inducedMap right) := by sorry
