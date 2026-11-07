-- Prove2me | Theorems.Thm_QEC_Distillation_sum_threeTag
-- name    : QEC.Distillation.sum_threeTag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:41:30.577336+00:00
-- url     : https://prove2.me/theorems/f0cb13b0-7429-4a47-acc6-247b10728362
-- title:
--   Distillation: sum three Tag
-- statement:
--   The Distillation construction uses the sum three Tag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L32-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L32-L36

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators

theorem QEC.Distillation.sum_threeTag {A R : Type} [Fintype A] [AddCommMonoid R]
    (f : (ThreeCopyTag → A) → R) :
    (∑ h, f h) = ∑ a, ∑ b, ∑ c, f (threeTagEquiv A (a, b, c)) := by sorry
