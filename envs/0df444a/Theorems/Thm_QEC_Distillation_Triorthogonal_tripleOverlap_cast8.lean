-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_tripleOverlap_cast8
-- name    : QEC.Distillation.Triorthogonal.tripleOverlap_cast8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:33:33.42163+00:00
-- url     : https://prove2.me/theorems/114c4bd8-1002-4030-ba52-13322b00a319
-- title:
--   Triorthogonal: triple Overlap cast8
-- statement:
--   Exact triple overlap, now viewed as a phase exponent modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L112-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L112-L121

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

theorem QEC.Distillation.Triorthogonal.tripleOverlap_cast8 (x y z : Word (ZMod 2) Index) :
    (BinaryRowFamily.tripleOverlap x y z : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) * bitLift8 (z p) := by sorry
