-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionWeight_smul_conditional_toOperator
-- name    : QEC.Distillation.HH18Parameterized.postselectionWeight_smul_conditional_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:16.110585+00:00
-- url     : https://prove2.me/theorems/11faaa20-30b2-4f76-924d-5fce4d8f36b6
-- title:
--   HH18 Parameterized: postselection Weight smul conditional to Operator
-- statement:
--   Reweighting a positive conditional endpoint recovers the literal raw
--   physical branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L133-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L133-L143

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
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

theorem QEC.Distillation.HH18Parameterized.postselectionWeight_smul_conditional_toOperator {w r m : Nat}
    (h : Admissible w r m) (rho : DensityOperator (PhysicalRegister m w))
    (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    (postselectionWeight h outcome rho : Complex) •
        (postselectionConditional h rho outcome hpositive).toOperator =
      rawPostselectionEndpoint h outcome rho := by sorry
