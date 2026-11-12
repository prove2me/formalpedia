-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolOutputCoordinate_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolOutputCoordinate_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:02:08.030852+00:00
-- url     : https://prove2.me/theorems/f973f9a3-2d58-4642-90d0-4b7c70fab5e6
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Output Coordinate card
-- statement:
--   The literal terminal-coordinate carrier has the actual output count
--   `q * k^z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L38-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L38-L55

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolOutputCoordinate_card
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) =
      q * logicalOutputCount m w ^ z := by sorry
