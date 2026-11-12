-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:20:40.894801+00:00
-- url     : https://prove2.me/theorems/2ed453d6-8e2f-4e4e-960e-c865610bdcf4
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Success Mass eq sum
-- statement:
--   The global success mass is exactly the finite sum of original physical
--   Born weights whose visible histories satisfy all routing requirements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L268-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L268-L280

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho =
      ∑ outcome ∈ Finset.univ.filter
          (fun outcome =>
            decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz outcome),
        (decodedRetryPoolPhysicalProtocolInstrument
          h hdegree z q hz).bornWeight outcome rho := by sorry
