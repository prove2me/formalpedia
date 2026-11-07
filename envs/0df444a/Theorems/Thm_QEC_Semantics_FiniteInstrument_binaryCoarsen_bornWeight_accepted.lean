-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_bornWeight_accepted
-- name    : QEC.Semantics.FiniteInstrument.binaryCoarsen_bornWeight_accepted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:42.329179+00:00
-- url     : https://prove2.me/theorems/6a81d86f-7cea-41e1-8050-0fd4321eefd6
-- title:
--   Finite Instrument: binary Coarsen born Weight accepted
-- statement:
--   The Finite Instrument construction uses the binary Coarsen born Weight accepted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L73-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteInstrumentBinaryRun.lean#L73-L81

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

theorem QEC.Semantics.FiniteInstrument.binaryCoarsen_bornWeight_accepted
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (rho : DensityOperator H) :
    (I.binaryCoarsen accepts).bornWeight .accepted rho =
      ∑ outcome ∈ Finset.univ.filter (fun outcome => accepts outcome),
        I.bornWeight outcome rho := by sorry
