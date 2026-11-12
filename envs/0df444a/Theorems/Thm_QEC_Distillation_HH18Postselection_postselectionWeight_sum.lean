-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionWeight_sum
-- name    : QEC.Distillation.HH18Postselection.postselectionWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:46:24.178459+00:00
-- url     : https://prove2.me/theorems/08ea4b2b-5600-464b-9029-9eb8f5a9c73b
-- title:
--   HH18 Postselection: postselection Weight sum
-- statement:
--   Accepted and rejected weights exhaust the complete joint measurement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L91-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L91-L97

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

theorem QEC.Distillation.HH18Postselection.postselectionWeight_sum (rho : DensityOperator PhysicalRegister) :
    postselectionWeight .accepted rho + postselectionWeight .rejected rho = 1 := by sorry
