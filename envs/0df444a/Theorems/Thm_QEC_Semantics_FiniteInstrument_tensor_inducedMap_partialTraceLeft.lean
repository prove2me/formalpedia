-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_inducedMap_partialTraceLeft
-- name    : QEC.Semantics.FiniteInstrument.tensor_inducedMap_partialTraceLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:38.927698+00:00
-- url     : https://prove2.me/theorems/671404d0-8c81-4e23-afef-1cc5949181d4
-- title:
--   Finite Instrument: tensor induced Map partial Trace Left
-- statement:
--   Tracing out the complete left local instrument after a tensor operation
--   leaves the right induced map acting on the actual input marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L230-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L230-L375

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensor_inducedMap_partialTraceLeft
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hI : I.kraus.Complete)
    (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        ((I.tensor J).kraus.inducedMap A) =
      J.kraus.inducedMap
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by sorry
