-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorWordWeight_sum
-- name    : QEC.Distillation.HH18Parameterized.errorWordWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:36:05.379881+00:00
-- url     : https://prove2.me/theorems/271d55f4-d450-49f1-9094-01bcf53a5a12
-- title:
--   HH18 Parameterized: error Word Weight sum
-- statement:
--   The physical error-word law is normalized over the actual finite site
--   type, without specializing or enumerating a concrete block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L84-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L84-L89

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

theorem QEC.Distillation.HH18Parameterized.errorWordWeight_sum (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    ∑ error : PhysicalErrorWord m w,
      HH18NoisyInput.errorWordWeight epsilon error = 1 := by sorry
