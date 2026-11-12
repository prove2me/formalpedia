-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
-- name    : QEC.Distillation.HH18Parameterized.rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:17.726485+00:00
-- url     : https://prove2.me/theorems/3d5ab605-c4ac-4136-96ef-fd15743ccfa5
-- title:
--   HH18 Parameterized: raw Postselection Endpoint eq zero of weight eq zero
-- statement:
--   A zero actual Born weight leaves the literal raw endpoint at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L103-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L103-L110

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

theorem QEC.Distillation.HH18Parameterized.rawPostselectionEndpoint_eq_zero_of_weight_eq_zero {w r m : Nat}
    (h : Admissible w r m) (outcome : DistillationOutcome)
    (rho : DensityOperator (PhysicalRegister m w))
    (hzero : postselectionWeight h outcome rho = 0) :
    rawPostselectionEndpoint h outcome rho = 0 := by sorry
