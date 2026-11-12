-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_injectedBranchOperator_eq_errorBranchOperator
-- name    : QEC.Distillation.HH18Parameterized.injectedBranchOperator_eq_errorBranchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:12.584187+00:00
-- url     : https://prove2.me/theorems/b160d112-61a9-4524-a077-c00b0c08d9f3
-- title:
--   HH18 Parameterized: injected Branch Operator eq error Branch Operator
-- statement:
--   Sitewise phase cancellation identifies the injected operator with its
--   actual Pauli-error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L138-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L138-L143

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.injectedBranchOperator_eq_errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    injectedBranchOperator h error outcomes =
      errorBranchOperator h hdegree error := by sorry
