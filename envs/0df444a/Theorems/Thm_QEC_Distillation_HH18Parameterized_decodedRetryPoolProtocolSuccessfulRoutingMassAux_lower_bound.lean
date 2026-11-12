-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingMassAux_lower_bound
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:29:17.244378+00:00
-- url     : https://prove2.me/theorems/b3f3f77c-f00d-45e8-ad8a-6584f52f1e0e
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Mass Aux lower bound
-- statement:
--   Through every bounded physical stage, the successful-routing mass is at
--   least one minus the sum of the literal aggregate shortage budgets already
--   incurred.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L29-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L29-L64

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z),
      1 - (∑ incurred : Fin (stage + 1),
          decodedRetryPoolStageAggregateShortageBudget
            w r m epsilon incurred.1) ≤
        decodedRetryPoolProtocolSuccessfulRoutingMassAux
          h hdegree z q hz stage hstage
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) := by sorry
