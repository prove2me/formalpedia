-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_four_mul_bitLift8_booleanXor_mul
-- name    : QEC.Distillation.Triorthogonal.four_mul_bitLift8_booleanXor_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:33:54.368094+00:00
-- url     : https://prove2.me/theorems/86c92e73-5950-4338-9628-ba7a09964be1
-- title:
--   Triorthogonal: four mul bit Lift8 boolean Xor mul
-- statement:
--   Four times a product of XORs is the product of the lifted linear sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L578-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L578-L589

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.four_mul_bitLift8_booleanXor_mul (xs ys : List (ZMod 2)) :
    4 * bitLift8 (booleanXor xs) * bitLift8 (booleanXor ys) =
      4 * (xs.map bitLift8).sum * (ys.map bitLift8).sum := by sorry
