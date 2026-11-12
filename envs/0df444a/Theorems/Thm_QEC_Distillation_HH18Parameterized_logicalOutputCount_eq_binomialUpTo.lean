-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_logicalOutputCount_eq_binomialUpTo
-- name    : QEC.Distillation.HH18Parameterized.logicalOutputCount_eq_binomialUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:55.706261+00:00
-- url     : https://prove2.me/theorems/68d107b8-af3c-4f4c-a53d-d7e45e4205be
-- title:
--   HH18 Parameterized: logical Output Count eq binomial Up To
-- statement:
--   The logical output count is the removed-coordinate cumulative binomial sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L58-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L58-L60

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.logicalOutputCount_eq_binomialUpTo (m w : Nat) :
    logicalOutputCount m w = binomialUpTo m w := by sorry
