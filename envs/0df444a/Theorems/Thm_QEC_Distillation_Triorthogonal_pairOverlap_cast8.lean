-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_pairOverlap_cast8
-- name    : QEC.Distillation.Triorthogonal.pairOverlap_cast8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:31:15.033476+00:00
-- url     : https://prove2.me/theorems/821fad8c-af57-49fb-9ab9-2871210564a9
-- title:
--   Triorthogonal: pair Overlap cast8
-- statement:
--   Exact pair overlap, now viewed as a phase exponent modulo eight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L102-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L102-L109

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

theorem QEC.Distillation.Triorthogonal.pairOverlap_cast8 (x y : Word (ZMod 2) Index) :
    (BinaryRowFamily.pairOverlap x y : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) := by sorry
