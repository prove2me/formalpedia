-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:28:09.040197+00:00
-- url     : https://prove2.me/theorems/de7a6631-5c55-4ced-bcaf-a45dd0f35c20
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Branch Operator Global Aux eq recursive
-- statement:
--   The selected marginal of the original complete physical-history event is
--   exactly its OOM-safe recursive finite-instrument construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L294-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L294-L316

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path rho =
        decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz rho stage hstage path := by sorry
