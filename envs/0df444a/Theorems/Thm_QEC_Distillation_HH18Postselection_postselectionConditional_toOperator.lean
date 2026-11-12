-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionConditional_toOperator
-- name    : QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:44:41.365198+00:00
-- url     : https://prove2.me/theorems/587e27a8-d057-4d19-a1b2-1c507d23c028
-- title:
--   HH18 Postselection: postselection Conditional to Operator
-- statement:
--   The normalized branch is exactly the inverse-weight scaling of its raw endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L116-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L116-L122

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
    (rho : DensityOperator PhysicalRegister) (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    (postselectionConditional rho outcome hpos).toOperator =
      ((postselectionWeight outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint outcome rho := by sorry

attribute [defeq] QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
