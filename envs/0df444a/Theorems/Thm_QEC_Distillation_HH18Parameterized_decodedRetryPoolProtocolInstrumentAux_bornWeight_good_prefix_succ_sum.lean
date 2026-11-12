-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_bornWeight_good_prefix_succ_sum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_bornWeight_good_prefix_succ_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:24:55.895201+00:00
-- url     : https://prove2.me/theorems/7941f618-4dd6-4359-be73-b6778a1905ad
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Instrument Aux born Weight good prefix succ sum
-- statement:
--   Completing the next physical stage also preserves the total Born mass of
--   the histories whose retained predecessor prefix already routes successfully.
--   This statement filters only on the prefix and sums every new observation; it
--   does not assert that the new sibling pools are independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/BornMass.lean#L63-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/BornMass.lean#L63-L104

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_bornWeight_good_prefix_succ_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    (∑ nextOutcome ∈ Finset.univ.filter
        (fun nextOutcome : decodedRetryPoolProtocolOutcomeAux
            m w z q (stage + 1) hstage =>
          decodedRetryPoolProtocolSuccessfulRoutingAux
            m w z q stage (by omega) nextOutcome.1 = true),
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho) =
      ∑ outcome ∈ Finset.univ.filter
          (fun outcome : decodedRetryPoolProtocolOutcomeAux
              m w z q stage (by omega) =>
            decodedRetryPoolProtocolSuccessfulRoutingAux
              m w z q stage (by omega) outcome = true),
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).bornWeight outcome rho := by sorry
