-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_noisyInput_toOperator
-- name    : QEC.Distillation.HH18Parameterized.noisyInput_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:35:57.250905+00:00
-- url     : https://prove2.me/theorems/06b53e9e-a4d5-4931-8ded-64b6cf161f4d
-- title:
--   HH18 Parameterized: noisy Input to Operator
-- statement:
--   The actual parameterized noisy input has the literal normalized product
--   mixture over physical Pauli-`Z` error branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L93-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Preparation.lean#L93-L101

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

theorem QEC.Distillation.HH18Parameterized.noisyInput_toOperator (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (m w : Nat) :
    (noisyInput epsilon m w).toOperator =
      ∑ error : PhysicalErrorWord m w,
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          (HH18NoisyInput.errorWordDensity error).toOperator := by sorry
