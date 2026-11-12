-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
-- name    : QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:19.790804+00:00
-- url     : https://prove2.me/theorems/492da332-f2e8-4230-99ad-5f53fec1289a
-- title:
--   HH18 Parameterized: postselection Conditional to Operator
-- statement:
--   The positive conditional endpoint is inverse-Born-weight scaling of the
--   literal raw endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L122-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L122-L129

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

theorem QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator {w r m : Nat}
    (h : Admissible w r m) (rho : DensityOperator (PhysicalRegister m w))
    (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    (postselectionConditional h rho outcome hpositive).toOperator =
      ((postselectionWeight h outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint h outcome rho := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
