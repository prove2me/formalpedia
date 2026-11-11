-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_two_mul_bitLift8_booleanXor
-- name    : QEC.Distillation.Triorthogonal.two_mul_bitLift8_booleanXor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:33:48.539803+00:00
-- url     : https://prove2.me/theorems/ad691b13-f949-4316-b39e-7e63dad914c8
-- title:
--   Triorthogonal: two mul bit Lift8 boolean Xor
-- statement:
--   Twice a binary XOR has only linear and quadratic terms modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L559-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L559-L566

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

theorem QEC.Distillation.Triorthogonal.two_mul_bitLift8_booleanXor (xs : List (ZMod 2)) :
    2 * bitLift8 (booleanXor xs) =
      2 * (xs.map bitLift8).sum - 4 * bitPairSum8 xs := by sorry
