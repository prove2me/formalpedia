-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_bitLift8_booleanXor
-- name    : QEC.Distillation.Triorthogonal.bitLift8_booleanXor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:30:36.877224+00:00
-- url     : https://prove2.me/theorems/90212781-d1a1-4c83-ad3f-8be2c9927131
-- title:
--   Triorthogonal: bit Lift8 boolean Xor
-- statement:
--   BH12 parity expansion truncated exactly modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L66-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L66-L78

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

theorem QEC.Distillation.Triorthogonal.bitLift8_booleanXor (xs : List (ZMod 2)) :
    bitLift8 (booleanXor xs) =
      booleanElementaryOne xs - 2 * booleanElementaryTwo xs +
        4 * booleanElementaryThree xs := by sorry
