-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathEnoughMassAux_zero
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:09:13.465676+00:00
-- url     : https://prove2.me/theorems/983bbbad-cc85-4f89-a2b5-9098072375b4
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Enough Mass Aux zero
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Path Enough Mass Aux zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L86-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L86-L101

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : routedDepthOutputSlots m w 0) :
    decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit 0 hz path =
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_zero
