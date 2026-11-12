-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionWeight_sum
-- name    : QEC.Distillation.HH18Parameterized.postselectionWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:26.811192+00:00
-- url     : https://prove2.me/theorems/5d96d099-8244-450a-894a-2fd035142ff3
-- title:
--   HH18 Parameterized: postselection Weight sum
-- statement:
--   Accepted and rejected Born weights exhaust the actual complete joint
--   measurement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L93-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L93-L100

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

theorem QEC.Distillation.HH18Parameterized.postselectionWeight_sum {w r m : Nat} (h : Admissible w r m)
    (rho : DensityOperator (PhysicalRegister m w)) :
    postselectionWeight h .accepted rho + postselectionWeight h .rejected rho = 1 := by sorry
