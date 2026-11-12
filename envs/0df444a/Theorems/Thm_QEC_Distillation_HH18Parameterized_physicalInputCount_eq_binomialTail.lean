-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalInputCount_eq_binomialTail
-- name    : QEC.Distillation.HH18Parameterized.physicalInputCount_eq_binomialTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:30.587677+00:00
-- url     : https://prove2.me/theorems/e0c80be0-3fc0-4c8c-b04d-b8ef28c9cdbe
-- title:
--   HH18 Parameterized: physical Input Count eq binomial Tail
-- statement:
--   The physical resource count is the retained-coordinate binomial tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L53-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L53-L55

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

theorem QEC.Distillation.HH18Parameterized.physicalInputCount_eq_binomialTail (m w : Nat) :
    physicalInputCount m w = binomialTail m w := by sorry
