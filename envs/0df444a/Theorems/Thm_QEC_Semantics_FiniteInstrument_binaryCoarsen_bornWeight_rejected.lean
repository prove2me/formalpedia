-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_bornWeight_rejected
-- name    : QEC.Semantics.FiniteInstrument.binaryCoarsen_bornWeight_rejected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:05.255421+00:00
-- url     : https://prove2.me/theorems/1be17990-1669-448c-bf2c-1906a4e05d5e
-- title:
--   Finite Instrument: binary Coarsen born Weight rejected
-- statement:
--   The Finite Instrument construction uses the binary Coarsen born Weight rejected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L83-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L83-L91

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

theorem QEC.Semantics.FiniteInstrument.binaryCoarsen_bornWeight_rejected
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .rejected rho =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => !accepts outcome),
        I.bornWeight outcome rho := by sorry
