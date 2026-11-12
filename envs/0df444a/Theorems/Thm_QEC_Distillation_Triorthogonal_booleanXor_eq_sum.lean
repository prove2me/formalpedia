-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_booleanXor_eq_sum
-- name    : QEC.Distillation.Triorthogonal.booleanXor_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:34:38.406198+00:00
-- url     : https://prove2.me/theorems/15f67ae0-2796-4618-b1de-ede83591280f
-- title:
--   Triorthogonal: boolean Xor eq sum
-- statement:
--   The Triorthogonal construction uses the boolean Xor eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L591-L595
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L591-L595

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

theorem QEC.Distillation.Triorthogonal.booleanXor_eq_sum (xs : List (ZMod 2)) :
    booleanXor xs = xs.sum := by sorry
