-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_four_mul_bitLift8_booleanXor
-- name    : QEC.Distillation.Triorthogonal.four_mul_bitLift8_booleanXor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:33:58.301205+00:00
-- url     : https://prove2.me/theorems/c2beab0b-0c50-4149-b707-5eea25e18ce8
-- title:
--   Triorthogonal: four mul bit Lift8 boolean Xor
-- statement:
--   Four times a binary XOR is linear modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L569-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L569-L575

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

theorem QEC.Distillation.Triorthogonal.four_mul_bitLift8_booleanXor (xs : List (ZMod 2)) :
    4 * bitLift8 (booleanXor xs) = 4 * (xs.map bitLift8).sum := by sorry
