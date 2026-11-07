-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
-- name    : QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:18.864994+00:00
-- url     : https://prove2.me/theorems/fdef3b98-d39a-497b-8c72-58a881219e42
-- title:
--   Finite Instrument: binary Distillation Run success Probability
-- statement:
--   The Finite Instrument construction uses the binary Distillation Run success Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L225-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L225-L236

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.FiniteInstrument
open Distillation
open scoped BigOperators
universe u v w
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]
variable {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]

theorem QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (resourceCount : Nat)
    (noisyInput : Fin resourceCount -> DensityOperator Resource)
    (prepareInput :
      (Fin resourceCount -> DensityOperator Resource) -> DensityOperator H)
    (fallback : DensityOperator K) :
    (binaryDistillationRun I accepts hI resourceCount noisyInput prepareInput
      fallback).successProbability =
      (I.binaryCoarsen accepts).bornWeight .accepted
        (prepareInput noisyInput) := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
