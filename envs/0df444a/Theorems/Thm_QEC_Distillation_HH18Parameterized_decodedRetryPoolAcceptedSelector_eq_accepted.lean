-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedSelector_eq_accepted
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedSelector_eq_accepted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:33.193607+00:00
-- url     : https://prove2.me/theorems/1b5cf0da-99df-41d7-b985-5fff25ac1c12
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Selector eq accepted
-- statement:
--   Every deterministic retry-pool selector slot contains an actually
--   accepted decoded outcome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L31-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L31-L43

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedSelector_eq_accepted
    (attempts : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card)
    (slot : Fin required) :
    tensorPowerHistoryAt DistillationOutcome attempts history
        (tensorPowerAcceptedSelector decodedRetryPoolAccepts attempts history
          required hrequired slot) = .accepted := by sorry
