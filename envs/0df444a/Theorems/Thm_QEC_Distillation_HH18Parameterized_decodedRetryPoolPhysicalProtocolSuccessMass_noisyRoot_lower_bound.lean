-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:29:17.426193+00:00
-- url     : https://prove2.me/theorems/fbbd4d65-68c9-40b1-8e43-5411764f8774
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Success Mass noisy Root lower bound
-- statement:
--   The accepted Born mass of the complete physical protocol is bounded below
--   by one minus the sum of all finite stage budgets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L68-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L68-L89

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    1 - (∑ stage : Fin z,
        decodedRetryPoolStageAggregateShortageBudget
          w r m epsilon stage.1) ≤
      decodedRetryPoolPhysicalProtocolSuccessMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by sorry
