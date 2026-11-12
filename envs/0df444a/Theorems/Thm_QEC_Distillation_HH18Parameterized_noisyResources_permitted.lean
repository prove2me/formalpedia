-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_noisyResources_permitted
-- name    : QEC.Distillation.HH18Parameterized.noisyResources_permitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:34:56.057901+00:00
-- url     : https://prove2.me/theorems/b05863e9-bbf5-456e-a27a-aa8e934d9745
-- title:
--   HH18 Parameterized: noisy Resources permitted
-- statement:
--   The constructed physical resource family is permitted by its independent
--   error model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L58-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L58-L65

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.noisyResources_permitted (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel m w epsilon))
      (noisyResources m w epsilon) := by sorry
