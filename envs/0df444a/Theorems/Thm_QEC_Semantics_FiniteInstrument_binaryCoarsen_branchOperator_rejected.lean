-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_branchOperator_rejected
-- name    : QEC.Semantics.FiniteInstrument.binaryCoarsen_branchOperator_rejected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:20:17.137898+00:00
-- url     : https://prove2.me/theorems/d4154ab1-e388-40a9-9fd8-cfab45071e76
-- title:
--   Finite Instrument: binary Coarsen branch Operator rejected
-- statement:
--   The Finite Instrument construction uses the binary Coarsen branch Operator rejected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L62-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L62-L71

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

theorem QEC.Semantics.FiniteInstrument.binaryCoarsen_branchOperator_rejected
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (A : Operator H) :
    (I.binaryCoarsen accepts).branchOperator .rejected A =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => !accepts outcome),
        I.branchOperator outcome A := by sorry
