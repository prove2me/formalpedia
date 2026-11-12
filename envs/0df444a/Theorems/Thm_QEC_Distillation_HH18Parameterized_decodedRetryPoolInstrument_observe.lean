-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_observe
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:31:30.26928+00:00
-- url     : https://prove2.me/theorems/eafe767f-869d-4c57-9249-8cf550dc475a
-- title:
--   HH18 Parameterized: decoded Retry Pool Instrument observe
-- statement:
--   The pool's visible outcome retains the actual decoded observed history and
--   only appends the terminal unit observation of the total selection channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L90-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Core.lean#L90-L105

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (firstIndex : tensorPowerHistory (decodedRawIndex h hdegree) attempts)
    (secondIndex : Fin ((tensorPowerHistoryConditionedChannel
      decodedRetryPoolAccepts attempts
      (((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex)
      required (LogicalSite m w)
      (decodedRetryPoolShortageState m w required)).chosenKrausCount)) :
    (decodedRetryPoolInstrument h hdegree attempts required).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex,
          PUnit.unit⟩ := by sorry
