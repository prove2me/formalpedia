-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
-- name    : QEC.Distillation.HH18Postselection.rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:49:55.302562+00:00
-- url     : https://prove2.me/theorems/9d02cfbd-9141-4d5b-b22f-aac0a5de412f
-- title:
--   HH18 Postselection: raw Postselection Endpoint eq zero of weight eq zero
-- statement:
--   A zero-weight coarse endpoint remains its literal raw zero operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L100-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L100-L106

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

theorem QEC.Distillation.HH18Postselection.rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
    (outcome : DistillationOutcome) (rho : DensityOperator PhysicalRegister)
    (hzero : postselectionWeight outcome rho = 0) :
    rawPostselectionEndpoint outcome rho = 0 := by sorry
