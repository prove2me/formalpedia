-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_logicalPlus_norm
-- name    : QEC.Distillation.HH18Parameterized.logicalPlus_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:57.926198+00:00
-- url     : https://prove2.me/theorems/e2e665f8-5ac5-4629-a8d2-7acdcc3ef2ab
-- title:
--   HH18 Parameterized: logical Plus norm
-- statement:
--   The logical-plus seed is normalized for every finite parameterized register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L79-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L79-L88

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

theorem QEC.Distillation.HH18Parameterized.logicalPlus_norm (m w : Nat) : ‖logicalPlus m w‖ = 1 := by sorry
