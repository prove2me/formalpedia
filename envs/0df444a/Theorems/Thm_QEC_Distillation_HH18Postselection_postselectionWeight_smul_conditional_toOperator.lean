-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionWeight_smul_conditional_toOperator
-- name    : QEC.Distillation.HH18Postselection.postselectionWeight_smul_conditional_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:50:55.254276+00:00
-- url     : https://prove2.me/theorems/c90ec06b-bff1-4b7e-abbe-081fdd4ea0d1
-- title:
--   HH18 Postselection: postselection Weight smul conditional to Operator
-- statement:
--   Weighting a positive conditional density recovers the physical raw endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L125-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L125-L134

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

theorem QEC.Distillation.HH18Postselection.postselectionWeight_smul_conditional_toOperator
    (rho : DensityOperator PhysicalRegister) (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    (postselectionWeight outcome rho : Complex) •
        (postselectionConditional rho outcome hpos).toOperator =
      rawPostselectionEndpoint outcome rho := by sorry
